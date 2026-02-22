import Lean
import Linglib.Theories.Pragmatics.RSA.Core.Verified
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.Reify

set_option autoImplicit false

/-!
# RSAPredict Proof Builder

Build compositional QInterval containment proofs (`CProof`), both generic
interval combinators and RSA-specific proof builders for L0, S1, and L1.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic
open Linglib.Interval

-- ============================================================================
-- CProof Structure
-- ============================================================================

/-- Result of building a compositional QInterval containment proof.
    Each CProof carries the interval Expr, its containment proof, and ℚ bounds. -/
structure CProof where
  iExpr : Expr
  proof : Expr
  lo : ℚ
  hi : ℚ
deriving Inhabited

instance : Inhabited CProof where
  default := ⟨default, default, 0, 0⟩

-- ============================================================================
-- Generic QInterval Combinators
-- ============================================================================

/-- Prove a ℚ proposition by `native_decide`. -/
def proveQPropND (type : Expr) : TacticM Expr := do
  let mvar ← mkFreshExprMVar type
  let saved ← getGoals
  setGoals [mvar.mvarId!]
  try evalTactic (← `(tactic| native_decide))
  catch e =>
    setGoals saved
    throwError "rsa_predict: native_decide failed on ℚ prop: {e.toMessageData}"
  setGoals saved
  return mvar

/-- Build CProof for a concrete ℚ value.
    Uses special lemmas for 0 and 1 to avoid Nat.cast/OfNat mismatch. -/
def buildExact (q : ℚ) : MetaM CProof := do
  if q == 0 then
    let qE ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
    let iExpr ← mkAppM ``QInterval.exact #[qE]
    return ⟨iExpr, mkConst ``QInterval.exact_zero_containsReal, 0, 0⟩
  else if q == 1 then
    let qE ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 1, none]
    let iExpr ← mkAppM ``QInterval.exact #[qE]
    return ⟨iExpr, mkConst ``QInterval.exact_one_containsReal, 1, 1⟩
  else if q.den == 1 && q.num ≥ 2 then
    let nExpr := mkRawNatLit q.num.toNat
    let qE ← mkAppOptM ``Nat.cast #[mkConst ``Rat, none, nExpr]
    let iExpr ← mkAppM ``QInterval.exact #[qE]
    let proof ← mkAppM ``QInterval.exact_natCast_containsReal #[nExpr]
    return ⟨iExpr, proof, q, q⟩
  else
    let qE ← mkRatExpr q
    let iExpr ← mkAppM ``QInterval.exact #[qE]
    let proof ← mkAppM ``QInterval.exact_containsReal #[qE]
    return ⟨iExpr, proof, q, q⟩

/-- Build CProof for x + y. -/
def buildCAdd (p1 p2 : CProof) : MetaM CProof := do
  let iExpr ← mkAppM ``QInterval.add #[p1.iExpr, p2.iExpr]
  let proof ← mkAppM ``QInterval.add_containsReal #[p1.proof, p2.proof]
  return ⟨iExpr, proof, p1.lo + p2.lo, p1.hi + p2.hi⟩

/-- Build right-folded sum matching Finset.sum reduction via List.foldr.
    For elements [e₁, e₂, e₃], builds f(e₁) + (f(e₂) + (f(e₃) + 0)). -/
def buildChainAdd (proofs : Array CProof) : MetaM CProof := do
  let mut result ← buildExact 0
  for i in (List.range proofs.size).reverse do
    result ← buildCAdd proofs[i]! result
  return result

/-- Build CProof for x * y (nonneg intervals). -/
def buildCMulNN (p1 p2 : CProof) : TacticM CProof := do
  let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
  let lo1 ← mkAppM ``QInterval.lo #[p1.iExpr]
  let lo2 ← mkAppM ``QInterval.lo #[p2.iExpr]
  let ha ← proveQPropND (← mkAppM ``LE.le #[zeroQ, lo1])
  let hb ← proveQPropND (← mkAppM ``LE.le #[zeroQ, lo2])
  let iExpr ← mkAppM ``QInterval.mulNonneg #[p1.iExpr, p2.iExpr, ha, hb]
  let proof ← mkAppM ``QInterval.mulNonneg_containsReal #[ha, hb, p1.proof, p2.proof]
  return ⟨iExpr, proof, p1.lo * p2.lo, p1.hi * p2.hi⟩

/-- Build CProof for x * y (general, handles negative factors via 4-corner method). -/
def buildCMulGen (p1 p2 : CProof) : TacticM CProof := do
  let iExpr ← mkAppM ``QInterval.mul #[p1.iExpr, p2.iExpr]
  let proof ← mkAppM ``QInterval.mul_containsReal #[p1.proof, p2.proof]
  let corners := #[p1.lo * p2.lo, p1.lo * p2.hi, p1.hi * p2.lo, p1.hi * p2.hi]
  let lo := corners.foldl min corners[0]!
  let hi := corners.foldl max corners[0]!
  return ⟨iExpr, proof, lo, hi⟩

/-- Build CProof for x * y, preferring nonneg if possible, falling back to general. -/
def buildCMulSafe (p1 p2 : CProof) : TacticM CProof := do
  if p1.lo ≥ 0 && p2.lo ≥ 0 then
    buildCMulNN p1 p2
  else
    buildCMulGen p1 p2

/-- Build CProof for -x using neg_containsReal. -/
def buildCNeg (p : CProof) : TacticM CProof := do
  let iExpr ← mkAppM ``QInterval.neg #[p.iExpr]
  let proof ← mkAppM ``QInterval.neg_containsReal #[p.proof]
  return ⟨iExpr, proof, -p.hi, -p.lo⟩

/-- Build CProof for x / y (nonneg numerator, positive denominator). -/
def buildCDivPos (num denom : CProof) : TacticM CProof := do
  let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
  let numLo ← mkAppM ``QInterval.lo #[num.iExpr]
  let denomLo ← mkAppM ``QInterval.lo #[denom.iExpr]
  let ha ← proveQPropND (← mkAppM ``LE.le #[zeroQ, numLo])
  let hb ← proveQPropND (← mkAppM ``LT.lt #[zeroQ, denomLo])
  let iExpr ← mkAppM ``QInterval.divPos #[num.iExpr, denom.iExpr, ha, hb]
  let proof ← mkAppM ``QInterval.divPos_containsReal #[ha, hb, num.proof, denom.proof]
  return ⟨iExpr, proof, num.lo / denom.hi, num.hi / denom.lo⟩

/-- Build CProof for policy: `if totalScore = 0 then 0 else score / totalScore`.
    Requires totalScore interval to have positive lo. -/
def buildPolicyProof (scoreProof totalProof : CProof) : TacticM CProof := do
  unless totalProof.lo > 0 do
    throwError "rsa_predict: policy proof requires total.lo > 0, got {totalProof.lo}"
  let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
  let totLo ← mkAppM ``QInterval.lo #[totalProof.iExpr]
  let loPos ← proveQPropND (← mkAppM ``LT.lt #[zeroQ, totLo])
  let neZero ← mkAppM ``QInterval.ne_zero_of_lo_pos #[totalProof.proof, loPos]
  let divProof ← buildCDivPos scoreProof totalProof
  let zeroR ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 0, none]
  let proof ← try
    mkAppOptM ``QInterval.ite_neg_containsReal
      #[none, none, none, some zeroR, none, some neZero, some divProof.proof]
  catch e =>
    let neZeroType ← inferType neZero
    let divType ← inferType divProof.proof
    throwError "rsa_predict: buildPolicyProof ite_neg_containsReal failed:\n  neZero type = {← ppExpr neZeroType}\n  divProof type = {← ppExpr divType}\n  error: {e.toMessageData}"
  return ⟨divProof.iExpr, proof, divProof.lo, divProof.hi⟩

/-- Build CProof for Real.exp(x). Uses expInterval_containsReal.
    Meta-level bounds use expPoint for ℚ approximation. -/
def buildCExp (p : CProof) : TacticM CProof := do
  let iExpr ← mkAppM ``Linglib.Interval.expInterval #[p.iExpr]
  let proof ← try
    mkAppM ``Linglib.Interval.expInterval_containsReal #[p.proof]
  catch e =>
    throwError "rsa_predict: buildCExp failed on expInterval_containsReal:\n  p.proof type = {← ppExpr (← inferType p.proof)}\n  inner error: {e.toMessageData}"
  let lo := (Linglib.Interval.expPoint p.lo).lo
  let hi := (Linglib.Interval.expPoint p.hi).hi
  return ⟨iExpr, proof, lo, hi⟩

/-- Build CProof for Real.log(x) where x > 0. Uses logInterval_containsReal. -/
def buildCLog (p : CProof) : TacticM CProof := do
  unless p.lo > 0 do
    throwError "rsa_predict: buildCLog requires lo > 0, got {p.lo}"
  let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
  let loExpr ← mkAppM ``QInterval.lo #[p.iExpr]
  let hI ← proveQPropND (← mkAppM ``LT.lt #[zeroQ, loExpr])
  let iExpr ← mkAppM ``Linglib.Interval.logInterval #[p.iExpr, hI]
  let proof ← mkAppM ``Linglib.Interval.logInterval_containsReal #[hI, p.proof]
  let (lo, _) := evalLogPoint p.lo
  let (_, hi) := evalLogPoint p.hi
  return ⟨iExpr, proof, lo, hi⟩

-- ============================================================================
-- Recursive Real Expression Proof Builder
-- ============================================================================

/-- Build CProof for an ℝ expression by recursively decomposing arithmetic structure.
    Handles fractions (like `1/3 : ℝ`), exp, log, ite, and other expressions that
    don't reduce to `↑(q : ℚ)` definitionally. Mirrors `matchArithOp`/`extractRat`
    and `reifyToRExpr` but outputs proof terms instead of ℚ values or RExpr.

    At each node, the proof refers to the (possibly unfolded) sub-expressions.
    The kernel accepts these because unfolded expressions are definitionally equal
    to the originals. -/
partial def buildRealExprProof (e : Expr) : TacticM CProof := do
  -- 1. Try nat literals (0, 1, 2, ...)
  if let some n := getNat? e then
    return ← buildExact (n : ℚ)
  -- 1b. isDefEq check for small numbers (handles Real.zero✝, Real.one✝ after whnf)
  -- Guard: only for expressions with ≤ 2 args (reduced Real values, not config field apps)
  -- Config expressions like cfg.meaning l u w (4+ args) go through whnf first (steps 10-12)
  let eType ← inferType e
  if eType.isConstOf ``Real && e.getAppNumArgs ≤ 2 then
    for n in ([0, 1, 2, 3] : List ℕ) do
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit n, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e target catch _ => return false
      if isEq then return ← buildExact (n : ℚ)
  -- 2. HDiv.hDiv a b (6 args: T₁ T₂ T₃ inst a b)
  if isAppOfMin e ``HDiv.hDiv 6 then
    let pa ← buildRealExprProof e.getAppArgs[4]!
    let pb ← buildRealExprProof e.getAppArgs[5]!
    if pa.lo ≥ 0 && pb.lo > 0 then
      return ← buildCDivPos pa pb
  -- Div.div a b (4 args)
  if isAppOfMin e ``Div.div 4 then
    let pa ← buildRealExprProof e.getAppArgs[2]!
    let pb ← buildRealExprProof e.getAppArgs[3]!
    if pa.lo ≥ 0 && pb.lo > 0 then
      return ← buildCDivPos pa pb
  -- 3. HMul.hMul a b (6 args)
  if isAppOfMin e ``HMul.hMul 6 then
    let pa ← buildRealExprProof e.getAppArgs[4]!
    let pb ← buildRealExprProof e.getAppArgs[5]!
    return ← buildCMulSafe pa pb
  -- Mul.mul a b (4 args)
  if isAppOfMin e ``Mul.mul 4 then
    let pa ← buildRealExprProof e.getAppArgs[2]!
    let pb ← buildRealExprProof e.getAppArgs[3]!
    return ← buildCMulSafe pa pb
  -- 4. HAdd.hAdd a b (6 args)
  if isAppOfMin e ``HAdd.hAdd 6 then
    let pa ← buildRealExprProof e.getAppArgs[4]!
    let pb ← buildRealExprProof e.getAppArgs[5]!
    return ← buildCAdd pa pb
  -- Add.add a b (4 args)
  if isAppOfMin e ``Add.add 4 then
    let pa ← buildRealExprProof e.getAppArgs[2]!
    let pb ← buildRealExprProof e.getAppArgs[3]!
    return ← buildCAdd pa pb
  -- 4b. Neg.neg (3 args: T inst a) — handles negation
  if isAppOfMin e ``Neg.neg 3 then
    let pa ← buildRealExprProof e.getAppArgs[2]!
    return ← buildCNeg pa
  -- 5. isDefEq-based matching (handles internal Real.mul, Real.add after whnf)
  let eType ← inferType e
  if eType.isConstOf ``Real then
    -- Binary ops
    if e.getAppNumArgs ≥ 2 then
      let a := e.getAppArgs[e.getAppNumArgs - 2]!
      let b := e.getAppArgs[e.getAppNumArgs - 1]!
      let isMul ← withNewMCtxDepth do
        try isDefEq e (← mkAppM ``HMul.hMul #[a, b]) catch _ => return false
      if isMul then
        let pa ← buildRealExprProof a
        let pb ← buildRealExprProof b
        return ← buildCMulSafe pa pb
      let isDiv ← withNewMCtxDepth do
        try isDefEq e (← mkAppM ``HDiv.hDiv #[a, b]) catch _ => return false
      if isDiv then
        let pa ← buildRealExprProof a
        let pb ← buildRealExprProof b
        if pa.lo ≥ 0 && pb.lo > 0 then
          return ← buildCDivPos pa pb
      let isAdd ← withNewMCtxDepth do
        try isDefEq e (← mkAppM ``HAdd.hAdd #[a, b]) catch _ => return false
      if isAdd then
        let pa ← buildRealExprProof a
        let pb ← buildRealExprProof b
        return ← buildCAdd pa pb
    -- Unary ops: Inv.inv (a⁻¹)
    if e.getAppNumArgs ≥ 1 then
      let a := e.getAppArgs.back!
      let isInv ← withNewMCtxDepth do
        try isDefEq e (← mkAppM ``Inv.inv #[a]) catch _ => return false
      if isInv then
        let pa ← buildRealExprProof a
        if pa.lo > 0 then
          -- Build 1/a proof, then convert to a⁻¹ via one_div
          let one ← buildExact 1
          let divProof ← buildCDivPos one pa
          -- one_div a : 1 / a = a⁻¹, so (one_div a).symm : a⁻¹ = 1 / a
          let oneDivPf ← mkAppM ``one_div #[a]
          let symPf ← mkAppM ``Eq.symm #[oneDivPf]
          let proof ← mkAppM ``QInterval.containsReal_of_eq #[symPf, divProof.proof]
          return ⟨divProof.iExpr, proof, divProof.lo, divProof.hi⟩
      -- Neg.neg (unary negation, handles Real.neg✝)
      let isNeg ← withNewMCtxDepth do
        try isDefEq e (← mkAppM ``Neg.neg #[a]) catch _ => return false
      if isNeg then
        let pa ← buildRealExprProof a
        return ← buildCNeg pa
  -- 6. Real.exp (direct or as (Complex.exp ↑x).re after unfolding)
  let fn := e.getAppFn
  if fn.isConstOf ``Real.exp && e.getAppNumArgs ≥ 1 then
    let inner := e.getAppArgs[0]!
    let innerProof ← buildRealExprProof inner
    return ← buildCExp innerProof
  -- 6b. (Complex.exp ↑x).re — unfolded form of Real.exp x
  --     e = Expr.proj ``Complex 0 (Complex.exp (Complex.ofReal x))
  if e.isProj then
    let projExpr := e.projExpr!
    let projFn := projExpr.getAppFn
    if projFn.isConstOf ``Complex.exp && projExpr.getAppNumArgs ≥ 1 then
      let cArg := projExpr.getAppArgs[0]!
      -- cArg is ↑x — unfold Complex.ofReal to get x, or use whnf fallback
      let mut realArg := cArg
      -- Try common patterns: Complex.ofReal x, or @Algebra.cast ℝ ℂ ... x
      if cArg.getAppFn.isConstOf ``Complex.ofReal then
        realArg := cArg.getAppArgs.back!
      else
        -- Try to find the ℝ argument via unfoldDefinition
        let mut cur := cArg
        for _ in List.range 5 do
          if cur.getAppFn.isConstOf ``Complex.ofReal then
            realArg := cur.getAppArgs.back!
            break
          if let some cur' ← unfoldDefinition? cur then
            cur := cur'.headBeta
          else break
      let argType ← inferType realArg
      unless argType.isConstOf ``Real do
        throwError "rsa_predict: Complex.exp handler: expected ℝ arg, got {← ppExpr argType}\n  realArg = {← ppExpr realArg}\n  cArg = {← ppExpr cArg}"
      let innerProof ← buildRealExprProof realArg
      return ← buildCExp innerProof
  -- 7. Real.log (positive argument only; log(0) = 0 handled via whnf fallback)
  if fn.isConstOf ``Real.log && e.getAppNumArgs ≥ 1 then
    let inner := e.getAppArgs[0]!
    let innerProof ← buildRealExprProof inner
    if innerProof.lo > 0 then
      return ← buildCLog innerProof
    else if innerProof.lo == 0 && innerProof.hi == 0 then
      -- log(0) = 0 by Lean convention: use log_zero_containsReal
      let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
      let loExpr ← mkAppM ``QInterval.lo #[innerProof.iExpr]
      let hiExpr ← mkAppM ``QInterval.hi #[innerProof.iExpr]
      let hlo ← proveQPropND (← mkAppM ``LE.le #[zeroQ, loExpr])
      let hhi ← proveQPropND (← mkAppM ``LE.le #[hiExpr, zeroQ])
      let proof ← mkAppM ``Linglib.Interval.log_zero_containsReal
        #[innerProof.proof, hlo, hhi]
      let zeroQExpr ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
      return ⟨← mkAppM ``QInterval.exact #[zeroQExpr], proof, 0, 0⟩
  -- 8. ite (if-then-else)
  if fn.isConstOf ``ite && e.getAppNumArgs ≥ 5 then
    let args := e.getAppArgs
    let cond := args[1]!
    let thenBr := args[3]!
    let elseBr := args[4]!
    -- For Bool equality conditions like `qualityOk ... = true`
    if cond.isAppOfArity ``Eq 3 then
      let condArgs := cond.getAppArgs
      if condArgs[0]!.isConstOf ``Bool then
        let boolVal ← whnf condArgs[1]!
        let rhsVal ← whnf condArgs[2]!
        let lhsIsTrue := boolVal.isConstOf ``Bool.true
        let lhsIsFalse := boolVal.isConstOf ``Bool.false
        let rhsIsTrue := rhsVal.isConstOf ``Bool.true
        let rhsIsFalse := rhsVal.isConstOf ``Bool.false
        if (lhsIsTrue && rhsIsTrue) || (lhsIsFalse && rhsIsFalse) then
          -- Condition is true: prove it via native_decide, take then branch
          let hc ← proveQPropND cond
          let brProof ← buildRealExprProof thenBr
          -- ite_pos needs y (else branch) explicitly since it's free
          let proof ← mkAppOptM ``QInterval.ite_pos_containsReal
            #[none, none, none, none, some elseBr, some hc, some brProof.proof]
          return ⟨brProof.iExpr, proof, brProof.lo, brProof.hi⟩
        else if (lhsIsTrue && rhsIsFalse) || (lhsIsFalse && rhsIsTrue) then
          -- Condition is false: prove ¬c via native_decide, take else branch
          let notCond ← mkAppM ``Not #[cond]
          let hc ← proveQPropND notCond
          let brProof ← buildRealExprProof elseBr
          -- ite_neg needs x (then branch) explicitly since it's free
          let proof ← mkAppOptM ``QInterval.ite_neg_containsReal
            #[none, none, none, some thenBr, none, some hc, some brProof.proof]
          return ⟨brProof.iExpr, proof, brProof.lo, brProof.hi⟩
      -- For numeric equality conditions like `totalScore = 0` — fall through to whnf
    -- Fallback: reduce the ite via whnf
    let e' ← whnf e
    if !e'.equal e then
      return ← buildRealExprProof e'
  -- 8b. Decidable.rec (from whnf'd ite with non-computable Decidable instance, e.g. over ℝ)
  if fn.isConstOf ``Decidable.rec && e.getAppNumArgs ≥ 5 then
    let args := e.getAppArgs
    let prop := args[0]!      -- the proposition p
    let isFalseBr := args[2]!  -- ¬p → ℝ
    let isTrueBr := args[3]!   -- p → ℝ
    let inst := args[4]!       -- Decidable p instance
    -- Handle `x = 0` pattern: build CProof for x, use bounds to determine branch
    if prop.isAppOfArity ``Eq 3 then
      let propArgs := prop.getAppArgs
      let rhs := propArgs[2]!
      if let some 0 := getOfNat? rhs then
        let lhs := propArgs[1]!
        let lhsProof ← buildRealExprProof lhs
        if lhsProof.lo > 0 then
          -- x > 0 so x ≠ 0: take isFalse branch
          let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
          let loExpr ← mkAppM ``QInterval.lo #[lhsProof.iExpr]
          let hlo ← proveQPropND (← mkAppM ``LT.lt #[zeroQ, loExpr])
          let hpos ← mkAppM ``QInterval.pos_of_lo_pos #[lhsProof.proof, hlo]
          -- ne_of_gt : a > b → a ≠ b; 0 < x means x > 0, gives x ≠ 0 = ¬(x = 0)
          let hnc ← mkAppM ``ne_of_gt #[hpos]
          let branchExpr := (Expr.app isFalseBr hnc).headBeta
          let brProof ← buildRealExprProof branchExpr
          let proof ← mkAppOptM ``QInterval.decidable_rec_neg_containsReal
            #[none, some inst, none, some isFalseBr, some isTrueBr, some hnc, some brProof.proof]
          return ⟨brProof.iExpr, proof, brProof.lo, brProof.hi⟩
        else if lhsProof.lo == 0 && lhsProof.hi == 0 then
          -- x = 0: take isTrue branch via eq_zero_of_contained_nonneg
          let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
          let loExpr ← mkAppM ``QInterval.lo #[lhsProof.iExpr]
          let hiExpr ← mkAppM ``QInterval.hi #[lhsProof.iExpr]
          let hlo ← proveQPropND (← mkAppM ``LE.le #[zeroQ, loExpr])
          let hhi ← proveQPropND (← mkAppM ``LE.le #[hiExpr, zeroQ])
          let hc ← mkAppM ``QInterval.eq_zero_of_contained_nonneg
            #[lhsProof.proof, hlo, hhi]
          let branchExpr := (Expr.app isTrueBr hc).headBeta
          let brProof ← buildRealExprProof branchExpr
          let proof ← mkAppOptM ``QInterval.decidable_rec_pos_containsReal
            #[none, some inst, none, some isFalseBr, some isTrueBr, some hc, some brProof.proof]
          return ⟨brProof.iExpr, proof, brProof.lo, brProof.hi⟩
  -- 9. Finset.sum / summation forms — unfold to additions via whnf
  let fnName := fn.constName?
  if fnName == some ``Finset.sum || fnName == some ``Multiset.sum ||
     fnName == some ``Multiset.fold || fnName == some ``List.foldr ||
     fnName == some ``List.foldl || fnName == some ``List.sum ||
     fnName == some ``Quot.lift then
    let e' ← whnf e
    if !e'.equal e then
      return ← buildRealExprProof e'
  -- 10. Try incremental unfolding (preserves operator structure)
  if let some e' ← unfoldDefinition? e then
    return ← buildRealExprProof e'.headBeta
  -- 11. Try reducible whnf (stops at noncomputable defs like Real.exp, Real.log)
  let eR ← withReducible do whnf e
  if !eR.equal e then
    return ← buildRealExprProof eR
  -- 12. Try full whnf (handles structure projections, ite reduction, etc.)
  let e' ← whnf e
  if !e'.equal e then
    return ← buildRealExprProof e'
  -- 13. Cauchy sequence form: { cauchy := ↑n } — search for nat literals in
  --     the reduced expression and check isDefEq against @OfNat.ofNat ℝ n _
  if (← inferType e).isConstOf ``Real then
    let rec collectNatLits (e : Expr) : Array ℕ :=
      match e.rawNatLit? with
      | some n => #[n]
      | none => e.getAppArgs.foldl (init := #[]) fun acc arg =>
          acc ++ collectNatLits arg
    let nats := (collectNatLits e).toList.eraseDups
    for n in nats do
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit n, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e target catch _ => return false
      if isEq then return ← buildExact (n : ℚ)
  throwError "rsa_predict: buildRealExprProof cannot decompose: {← ppExpr e}\n  fn = {e.getAppFn}\n  fnName = {e.getAppFn.constName?}\n  isProj = {e.isProj}"

/-- Build CProof for a concrete ℚ value matching a specific real expression.
    Pre-reduces the expression via `whnf` so that structural matching (getNat?,
    isAppOfMin) catches it immediately, avoiding redundant `isDefEq` calls on
    unreduced config field expressions. -/
def buildLeaf (_q : ℚ) (realExpr : Expr) : TacticM CProof := do
  -- whnf the expression once so structural checks in buildRealExprProof work
  -- immediately (avoids 5+ redundant isDefEq reductions per leaf)
  let reduced ← whnf realExpr
  buildRealExprProof reduced

-- ============================================================================
-- RSA-Specific Compositional Builders
-- ============================================================================

/-- Build CProof for (cfg.L0agent l).policy u w.
    Uses `buildLeaf` so each meaning proof mentions the actual `cfg.meaning`
    expression, allowing compositions to carry the correct real-valued type. -/
def buildL0PolicyCProof (cfg l u : Expr)
    (allWElems : Array Expr) (wIdx : ℕ) : TacticM CProof := do
  let mut meaningProofs : Array CProof := #[]
  for w' in allWElems do
    let mExpr ← mkAppM ``RSA.RSAConfig.meaning #[cfg, l, u, w']
    let q ← extractRat mExpr
    meaningProofs := meaningProofs.push (← buildLeaf q mExpr)
  let totalProof ← buildChainAdd meaningProofs
  let scoreProof := meaningProofs[wIdx]!
  if totalProof.lo > 0 then
    buildPolicyProof scoreProof totalProof
  else if scoreProof.hi == 0 then
    -- This world's meaning is 0 → score = 0 → policy = 0 (regardless of total)
    let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
    let sloExpr ← mkAppM ``QInterval.lo #[scoreProof.iExpr]
    let shiExpr ← mkAppM ``QInterval.hi #[scoreProof.iExpr]
    let hlo ← proveQPropND (← mkEq sloExpr zeroQ)
    let hhi ← proveQPropND (← mkEq shiExpr zeroQ)
    -- meaning l u w = 0
    let scoreEqZero ← mkAppM ``QInterval.eq_zero_of_containsReal
      #[scoreProof.proof, hlo, hhi]
    -- L0agent.score = meaning, so score = 0 (definitional)
    let l0Agent ← mkAppM ``RSA.RSAConfig.L0agent #[cfg, l]
    let w := allWElems[wIdx]!
    -- policy = 0 from score = 0
    let policyEqZero ← mkAppM ``Core.RationalAction.policy_eq_zero_of_score_eq_zero
      #[l0Agent, u, w, scoreEqZero]
    -- (exact 0).containsReal 0 → (exact 0).containsReal (policy u w)
    let zeroProof := mkConst ``QInterval.exact_zero_containsReal
    let proof ← mkAppM ``QInterval.containsReal_of_eq #[policyEqZero, zeroProof]
    return ⟨(← buildExact 0).iExpr, proof, 0, 0⟩
  else
    throwError "rsa_predict: L0 policy proof failed: total.lo={totalProof.lo}, score≠0"

/-- Check whether cfg.s1Score uses rpow (belief-based) or exp (action-based).
    Inspects the whnf of `cfg.s1Score` structurally — no kernel reduction needed
    beyond one config field unfold. Computed once per theorem and cached. -/
partial def exprContainsConst (name : Name) : Expr → Bool
  | .const n _ => n == name
  | .app f a => exprContainsConst name f || exprContainsConst name a
  | .lam _ t b _ => exprContainsConst name t || exprContainsConst name b
  | .forallE _ t b _ => exprContainsConst name t || exprContainsConst name b
  | .letE _ t v b _ =>
    exprContainsConst name t || exprContainsConst name v || exprContainsConst name b
  | .mdata _ e => exprContainsConst name e
  | .proj _ _ e => exprContainsConst name e
  | _ => false

def detectBeliefBased (cfg : Expr) : TacticM Bool := do
  let s1ScoreExpr ← mkAppM ``RSA.RSAConfig.s1Score #[cfg]
  let reduced ← whnf s1ScoreExpr
  return exprContainsConst ``Real.rpow reduced

/-- Build CProof for (cfg.S1agent l).score w u.
    Fast path: belief-based scoring (rpow(L0,α)) — uses rpowOne_containsReal.
    Slow path: generic decomposition via buildRealExprProof for action-based
    scoring (exp/log/sum, as in GoodmanStuhlmuller2013). -/
def buildS1ScoreCProof (cfg l w u : Expr)
    (allWElems : Array Expr) (αNat : ℕ) (isBeliefBased : Bool) : TacticM CProof := do
  -- Belief-based rpow path (works for FG2012-style models)
  if isBeliefBased then
    let wIdx ← findElemIdx allWElems w
    let l0Proof ← buildL0PolicyCProof cfg l u allWElems wIdx
    if αNat == 1 then
      let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
      let lo ← mkAppM ``QInterval.lo #[l0Proof.iExpr]
      let ha ← proveQPropND (← mkAppM ``LE.le #[zeroQ, lo])
      let proof ← mkAppM ``Linglib.Interval.rpowOne_containsReal #[ha, l0Proof.proof]
      return ⟨l0Proof.iExpr, proof, l0Proof.lo, l0Proof.hi⟩
    else
      throwError "rsa_predict: belief-based with α≠1 not yet supported"
  -- Action-based: decompose the actual S1 score expression
  let s1Agent ← mkAppM ``RSA.RSAConfig.S1agent #[cfg, l]
  let scoreExpr ← mkAppM ``Core.RationalAction.score #[s1Agent, w, u]
  -- Pre-whnf so buildRealExprProof's structural checks work immediately
  let reduced ← whnf scoreExpr
  buildRealExprProof reduced

/-- Build `∀ a', a' ≠ target → agent.score s a' = 0` from individual zero CProofs.
    Uses the inductive type's `casesOn` recursor to case-split on `a'`,
    providing the zero proof for each non-target constructor and `absurd rfl h`
    for the target constructor (contradiction). -/
def buildForallScoreZero (agent s : Expr)
    (allElems : Array Expr) (targetIdx : ℕ)
    (scoreProofs : Array CProof) : TacticM Expr := do
  let target := allElems[targetIdx]!
  let aType ← inferType target
  let aType' ← whnf aType
  -- Get inductive type info
  let typeName ← match aType'.getAppFn with
    | .const name _ => pure name
    | _ => throwError "buildForallScoreZero: action type {← ppExpr aType'} is not inductive"
  let env ← getEnv
  let some (.inductInfo iv) := env.find? typeName
    | throwError "buildForallScoreZero: {typeName} is not an inductive type"
  let casesOnName := typeName ++ `casesOn
  let tArgs := aType'.getAppArgs
  let typeLevels := match aType'.getAppFn with
    | .const _ ls => ls
    | _ => []
  -- casesOn universe levels: motive universe (0 for Prop) ++ type params
  let casesOnLevels := levelZero :: typeLevels
  let casesOnConst := mkConst casesOnName casesOnLevels
  let zeroR ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 0, none]
  -- Build zero proofs (score = 0) for each non-target element
  let mut zeroProofExprs : Array Expr := #[]
  let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
  for i in [:allElems.size] do
    if i == targetIdx then
      zeroProofExprs := zeroProofExprs.push (mkConst ``True.intro) -- placeholder
    else
      let sp := scoreProofs[i]!
      let sloExpr ← mkAppM ``QInterval.lo #[sp.iExpr]
      let shiExpr ← mkAppM ``QInterval.hi #[sp.iExpr]
      let hlo ← proveQPropND (← mkEq sloExpr zeroQ)
      let hhi ← proveQPropND (← mkEq shiExpr zeroQ)
      let eqZero ← mkAppM ``QInterval.eq_zero_of_containsReal #[sp.proof, hlo, hhi]
      zeroProofExprs := zeroProofExprs.push eqZero
  -- Build motive: fun (x : A) => x ≠ target → agent.score s x = 0
  let motive ← withLocalDeclD `x aType fun x => do
    let neType ← mkAppM ``Ne #[x, target]
    let scoreApp ← mkAppM ``Core.RationalAction.score #[agent, s, x]
    let eqType ← mkEq scoreApp zeroR
    mkLambdaFVars #[x] (← mkArrow neType eqType)
  -- Build branches for casesOn
  let mut branches : Array Expr := #[]
  for i in [:iv.ctors.length] do
    let ci := allElems[i]!
    let neType ← mkAppM ``Ne #[ci, target]
    let br ← if i == targetIdx then
      -- Target: fun (h : target ≠ target) => absurd rfl h
      withLocalDeclD `h neType fun h => do
        let rflP ← mkAppM ``Eq.refl #[ci]
        let scoreApp ← mkAppM ``Core.RationalAction.score #[agent, s, ci]
        let goalType ← mkEq scoreApp zeroR
        let absurdP ← mkAppOptM ``absurd #[none, some goalType, some rflP, some h]
        mkLambdaFVars #[h] absurdP
    else
      -- Non-target: fun (_ : ci ≠ target) => zeroProof_i
      withLocalDeclD `h neType fun h => do
        mkLambdaFVars #[h] zeroProofExprs[i]!
    branches := branches.push br
  -- Assemble: fun (x : A) (h : x ≠ target) =>
  --   @A.casesOn.{0} tArgs... motive x br₀ br₁ ... h
  withLocalDeclD `x aType fun x => do
    withLocalDeclD `h (← mkAppM ``Ne #[x, target]) fun h => do
      let base := tArgs.foldl (init := casesOnConst) fun acc arg => mkApp acc arg
      let withMotiveAndMajor := mkApp (mkApp base motive) x
      let withBranches := branches.foldl (init := withMotiveAndMajor)
        fun acc br => mkApp acc br
      mkLambdaFVars #[x, h] (mkApp withBranches h)

/-- Build CProof for cfg.S1 l w u = (cfg.S1agent l).policy w u. -/
def buildS1PolicyCProof (cfg l w : Expr)
    (allWElems allUElems : Array Expr) (uIdx : ℕ) (αNat : ℕ)
    (isBeliefBased : Bool) : TacticM CProof := do
  let mut scoreProofs : Array CProof := #[]
  for u' in allUElems do
    scoreProofs := scoreProofs.push (← buildS1ScoreCProof cfg l w u' allWElems αNat isBeliefBased)
  let totalProof ← buildChainAdd scoreProofs
  let scoreProof := scoreProofs[uIdx]!
  -- Check for self-cancellation: all non-target scores are zero, target is positive.
  -- This avoids interval widening from divPos when score / totalScore = score / score.
  let allOthersZero := (List.range scoreProofs.size).all fun i =>
    i == uIdx || (scoreProofs[i]!.lo == 0 && scoreProofs[i]!.hi == 0)
  if allOthersZero && scoreProof.lo > 0 then
    -- Self-cancellation: policy = 1 (score is the only nonzero, so total = score)
    let s1Agent ← mkAppM ``RSA.RSAConfig.S1agent #[cfg, l]
    let target := allUElems[uIdx]!
    -- Build h_zeros: ∀ a', a' ≠ target → score w a' = 0
    let hZeros ← buildForallScoreZero s1Agent w allUElems uIdx scoreProofs
    -- Build h_sum: totalScore w = score w target (via Fintype.sum_eq_single)
    let hSum ← mkAppM ``Fintype.sum_eq_single #[target, hZeros]
    -- Build h_pos: 0 < score w target
    let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
    let lo ← mkAppM ``QInterval.lo #[scoreProof.iExpr]
    let hloLt ← proveQPropND (← mkAppM ``LT.lt #[zeroQ, lo])
    let hpos ← mkAppM ``QInterval.pos_of_lo_pos #[scoreProof.proof, hloLt]
    -- policy_eq_one_of_totalScore_eq: totalScore = score → 0 < score → policy = 1
    let policyEqOne ← mkAppM ``Core.RationalAction.policy_eq_one_of_totalScore_eq
      #[s1Agent, w, target, hSum, hpos]
    -- Wrap: (exact 1).containsReal (policy w target) via containsReal_of_eq
    let oneProof := mkConst ``QInterval.exact_one_containsReal
    let proof ← mkAppM ``QInterval.containsReal_of_eq #[policyEqOne, oneProof]
    let oneQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 1, none]
    let iExpr ← mkAppM ``QInterval.exact #[oneQ]
    return ⟨iExpr, proof, 1, 1⟩
  else if totalProof.lo > 0 then
    buildPolicyProof scoreProof totalProof
  else if scoreProof.hi == 0 then
    -- S1 score for this utterance is 0 → S1 policy is 0
    let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
    let sloExpr ← mkAppM ``QInterval.lo #[scoreProof.iExpr]
    let shiExpr ← mkAppM ``QInterval.hi #[scoreProof.iExpr]
    let hlo ← proveQPropND (← mkEq sloExpr zeroQ)
    let hhi ← proveQPropND (← mkEq shiExpr zeroQ)
    let scoreEqZero ← mkAppM ``QInterval.eq_zero_of_containsReal
      #[scoreProof.proof, hlo, hhi]
    let s1Agent ← mkAppM ``RSA.RSAConfig.S1agent #[cfg, l]
    let u := allUElems[uIdx]!
    let policyEqZero ← mkAppM ``Core.RationalAction.policy_eq_zero_of_score_eq_zero
      #[s1Agent, w, u, scoreEqZero]
    let zeroProof := mkConst ``QInterval.exact_zero_containsReal
    let proof ← mkAppM ``QInterval.containsReal_of_eq #[policyEqZero, zeroProof]
    return ⟨(← buildExact 0).iExpr, proof, 0, 0⟩
  else
    throwError "rsa_predict: S1 policy proof failed: total.lo={totalProof.lo}, score≠0"

/-- Build CProof for cfg.L1agent.score u w =
    worldPrior(w) * ∑ l, latentPrior(w,l) * S1(l,w,u). -/
def buildL1ScoreCProof (cfg u w : Expr)
    (allUElems allWElems allLElems : Array Expr)
    (wpValues lpValues : Array ℚ) (αNat : ℕ) (isBeliefBased : Bool) : TacticM CProof := do
  let wIdx ← findElemIdx allWElems w
  let uIdx ← findElemIdx allUElems u
  let nL := allLElems.size
  let wpExpr ← mkAppM ``RSA.RSAConfig.worldPrior #[cfg, w]
  let wpProof ← buildLeaf wpValues[wIdx]! wpExpr
  let mut latentTermProofs : Array CProof := #[]
  for lIdx in List.range allLElems.size do
    let l := allLElems[lIdx]!
    let lpQ := lpValues[wIdx * nL + lIdx]!
    let lpExpr ← mkAppM ``RSA.RSAConfig.latentPrior #[cfg, w, l]
    let lpProof ← buildLeaf lpQ lpExpr
    let s1Proof ← buildS1PolicyCProof cfg l w allWElems allUElems uIdx αNat isBeliefBased
    let termProof ← buildCMulNN lpProof s1Proof
    latentTermProofs := latentTermProofs.push termProof
  let latentSumProof ← buildChainAdd latentTermProofs
  buildCMulNN wpProof latentSumProof

end Linglib.Tactics.RSAPredict
