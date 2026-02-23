import Lean
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict.Helpers

set_option autoImplicit false

/-!
# RSAPredict Reifier

Convert `Expr : ℝ` to `MetaBounds` via memoized recursive reification,
and extract ℚ values from ℝ expressions.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic
open Linglib.Interval

-- ============================================================================
-- ℚ Extraction from ℝ Expressions
-- ============================================================================

def evalLogPoint (q : ℚ) : ℚ × ℚ :=
  if h : 0 < q then
    let I := Linglib.Interval.logPoint q h
    (I.lo, I.hi)
  else (0, 0)

/-- Scan an expression for an embedded raw natural number literal.
    After whnf reduces `n : ℝ` to its Cauchy sequence form, the natural
    number is typically buried inside `@Nat.cast ℚ _ n` or similar.
    This scans the expression tree (limited depth) for the first raw nat literal. -/
partial def findEmbeddedNat (e : Expr) (depth : ℕ := 15) : Option ℕ :=
  if depth == 0 then none
  else if let some n := e.rawNatLit? then some n
  else e.getAppArgs.findSome? (findEmbeddedNat · (depth - 1))

/-- Extract a ℤ from an expression in constructor form (Int.ofNat n or Int.negSucc n). -/
def extractIntExpr (e : Expr) : MetaM (Option ℤ) := do
  let e' ← whnf e
  if e'.isAppOfArity ``Int.ofNat 1 then
    let n ← whnf e'.getAppArgs[0]!
    return n.rawNatLit?.map Int.ofNat
  else if e'.isAppOfArity ``Int.negSucc 1 then
    let n ← whnf e'.getAppArgs[0]!
    return n.rawNatLit?.map Int.negSucc
  else if let some n := e'.rawNatLit? then
    return some (Int.ofNat n)
  else
    return none

/-- Extract ℚ from a Real.ofCauchy expression by evaluating the Cauchy sequence
    at index 0 and reading the resulting ℚ literal.

    CauSeq ℚ abs is a Subtype { val : ℕ → ℚ // IsCauSeq abs val }, so we project
    .val (field 0 of Subtype), apply to 0, and whnf-reduce to get a concrete Rat
    constructor (Rat.mk num den proof₁ proof₂). Then project .num and .den to
    extract the ℚ value.

    This handles fractions (2/3, 1/3, etc.) that findEmbeddedNat cannot,
    since findEmbeddedNat only scans for the first raw nat literal. -/
def extractRatFromCauchy (e : Expr) : MetaM (Option ℚ) := do
  let args := e.getAppArgs
  if args.isEmpty then return none
  let seq := args.back!
  -- Project Subtype.val (field 0), apply to 0, and reduce
  let fAtZero ← whnf (mkApp (mkProj ``Subtype 0 seq) (mkRawNatLit 0))
  -- Project Rat.num (field 0) and Rat.den (field 1)
  let numExpr ← whnf (mkProj ``Rat 0 fAtZero)
  let denExpr ← whnf (mkProj ``Rat 1 fAtZero)
  let some den := denExpr.rawNatLit? | return none
  if den == 0 then return none
  let some num ← extractIntExpr numExpr | return none
  return some (mkRat num den)

-- ============================================================================
-- Recursive Reifier
-- ============================================================================

def maxDepth : ℕ := 200

/-- Memoization cache for reifyToRExpr, keyed on Expr structural hash. -/
abbrev ReifyCache := IO.Ref (Std.HashMap UInt64 (Expr × MetaBounds))
/-- Store result in cache and return it. -/
private def cacheReturn (cache : ReifyCache) (key : UInt64) (result : Expr × MetaBounds) :
    MetaM (Expr × MetaBounds) := do
  cache.modify fun m => m.insert key result
  return result

/-- Simplified RExpr reifier for rsa_predict.
    Produces RExpr values + meta-level bounds.
    Uses a hash-keyed cache to avoid redundant reification of shared subexpressions. -/
partial def reifyToRExpr (cache : ReifyCache) (e : Expr) (depth : ℕ) :
    MetaM (Expr × MetaBounds) := do
  if depth == 0 then
    throwError "rsa_predict: max reification depth on: {← ppExpr e}"

  -- Let binding: substitute
  if e.isLet then
    return ← reifyToRExpr cache (e.letBody!.instantiate1 e.letValue!) (depth - 1)

  -- Cache lookup
  let key := hash e
  if let some result := (← cache.get).get? key then
    return result

  -- Natural literal
  if let some n := getOfNat? e then
    let rexpr ← mkAppM ``RExpr.nat #[mkRawNatLit n]
    return ← cacheReturn cache key (rexpr, ⟨n, n⟩)

  let fn := e.getAppFn
  let args := e.getAppArgs

  -- Cauchy-form ℝ literal: Real.ofCauchy wraps a constant Cauchy sequence.
  -- Extract the ℚ value by evaluating the sequence at index 0.
  if fn.isConstOf ``Real.ofCauchy then
    if let some q ← extractRatFromCauchy e then
      if q.den == 1 && q.num ≥ 0 then
        let n := q.num.toNat
        let rexpr ← mkAppM ``RExpr.nat #[mkRawNatLit n]
        return ← cacheReturn cache key (rexpr, ⟨n, n⟩)
      else
        -- Fraction or negative: build RExpr.div (possibly with RExpr.neg)
        let numE ← mkAppM ``RExpr.nat #[mkRawNatLit q.num.natAbs]
        let denE ← mkAppM ``RExpr.nat #[mkRawNatLit q.den]
        let divE ← mkAppM ``RExpr.div #[numE, denE]
        let rexpr ← if q.num < 0 then mkAppM ``RExpr.neg #[divE] else pure divE
        return ← cacheReturn cache key (rexpr, ⟨q, q⟩)
    -- Fallback: scan for embedded nat (handles cases where Cauchy structure is unusual)
    if let some n := findEmbeddedNat e then
      let rexpr ← mkAppM ``RExpr.nat #[mkRawNatLit n]
      return ← cacheReturn cache key (rexpr, ⟨n, n⟩)

  -- Addition: @HAdd.hAdd ℝ ℝ ℝ _ a b
  if isAppOfMin e ``HAdd.hAdd 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.add #[ra, rb]
    return ← cacheReturn cache key (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)

  if isAppOfMin e ``Add.add 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.add #[ra, rb]
    return ← cacheReturn cache key (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)

  -- Multiplication
  if isAppOfMin e ``HMul.hMul 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.mul #[ra, rb]
    return ← cacheReturn cache key (rexpr, metaEvalMul ba bb)

  if isAppOfMin e ``Mul.mul 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.mul #[ra, rb]
    return ← cacheReturn cache key (rexpr, metaEvalMul ba bb)

  -- Division
  if isAppOfMin e ``HDiv.hDiv 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.div #[ra, rb]
    let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                  else ⟨-1, 1⟩
    return ← cacheReturn cache key (rexpr, bounds)

  if isAppOfMin e ``Div.div 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.div #[ra, rb]
    let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                  else ⟨-1, 1⟩
    return ← cacheReturn cache key (rexpr, bounds)

  -- Negation
  if isAppOfMin e ``Neg.neg 3 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.neg #[ra]
    return ← cacheReturn cache key (rexpr, ⟨-ba.hi, -ba.lo⟩)

  -- Subtraction
  if isAppOfMin e ``HSub.hSub 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.sub #[ra, rb]
    return ← cacheReturn cache key (rexpr, ⟨ba.lo - bb.hi, ba.hi - bb.lo⟩)

  if isAppOfMin e ``Sub.sub 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.sub #[ra, rb]
    return ← cacheReturn cache key (rexpr, ⟨ba.lo - bb.hi, ba.hi - bb.lo⟩)

  -- Real.rpow
  if fn.isConstOf ``Real.rpow && args.size ≥ 2 then
    if let some n ← resolveNat? args[1]! then
      let (rb, bb) ← reifyToRExpr cache args[0]! (depth - 1)
      let rexpr ← mkAppM ``RExpr.rpow #[rb, mkRawNatLit n]
      let bounds := if n == 0 then ⟨1, 1⟩
                    else if bb.lo ≥ 0 then ⟨bb.lo ^ n, bb.hi ^ n⟩
                    else ⟨0, 1⟩
      return ← cacheReturn cache key (rexpr, bounds)
    if let some e' ← unfoldDefinition? e then
      return ← reifyToRExpr cache e' (depth - 1)

  -- Real.exp — with exp-log algebraic simplification
  -- exp(α*(log(x)-c)) = x^α * exp(-α*c), avoiding expensive logPoint calls.
  -- logPoint (50 bisection iterations of Padé ℚ arithmetic) is 98% of reification time.
  if fn.isConstOf ``Real.exp && args.size ≥ 1 then
    let inner := args[0]!
    -- Try to decompose: inner = α * rest, or just rest with α=1
    let (αExprOpt, rest) :=
      if isAppOfMin inner ``HMul.hMul 6 then
        (some (inner.getAppArgs[4]!), inner.getAppArgs[5]!)
      else if isAppOfMin inner ``Mul.mul 4 then
        (some (inner.getAppArgs[2]!), inner.getAppArgs[3]!)
      else (none, inner)
    -- Try to decompose: rest = log(x) - c, or just log(x) with c=0
    let (logCandidate, cExprOpt) :=
      if isAppOfMin rest ``HSub.hSub 6 then
        (rest.getAppArgs[4]!, some (rest.getAppArgs[5]!))
      else if isAppOfMin rest ``Sub.sub 4 then
        (rest.getAppArgs[2]!, some (rest.getAppArgs[3]!))
      else (rest, none)
    -- Check if logCandidate is Real.log(x)
    if logCandidate.getAppFn.isConstOf ``Real.log && logCandidate.getAppNumArgs ≥ 1 then
      let xExpr := logCandidate.getAppArgs[0]!
      -- Only do algebraic decomposition if α or c are actually present in the original
      -- (don't synthesize 1* or -0 wrappers that break the rfl bridge)
      if αExprOpt.isSome || cExprOpt.isSome then
        let (αRExpr, αBounds) ← match αExprOpt with
          | some e => reifyToRExpr cache e (depth - 1)
          | none => do
            let r ← mkAppM ``RExpr.nat #[mkRawNatLit 1]
            pure (r, (⟨1, 1⟩ : MetaBounds))
        if αBounds.lo == αBounds.hi && αBounds.lo > 0 && αBounds.lo.den == 1 then
          let α := αBounds.lo
          let n := α.num.toNat
          let (xRExpr, xBounds) ← reifyToRExpr cache xExpr (depth - 1)
          if xBounds.lo ≥ 0 then
            let (cRExpr, cBounds) ← match cExprOpt with
              | some e => reifyToRExpr cache e (depth - 1)
              | none => do
                let r ← mkAppM ``RExpr.nat #[mkRawNatLit 0]
                pure (r, (⟨0, 0⟩ : MetaBounds))
            -- x^n bounds (nonneg x, positive integer n → monotone increasing)
            let xPowBounds : MetaBounds :=
              if n == 1 then xBounds else ⟨xBounds.lo ^ n, xBounds.hi ^ n⟩
            -- exp(-n*c) bounds (exp monotone: use lo_arg for lo, hi_arg for hi)
            let expFactorBounds : MetaBounds :=
              let lo_arg := -(α * cBounds.hi)
              let hi_arg := -(α * cBounds.lo)
              if lo_arg == 0 && hi_arg == 0 then ⟨1, 1⟩
              else ⟨(Linglib.Interval.expPoint lo_arg).lo,
                    (Linglib.Interval.expPoint hi_arg).hi⟩
            let bounds := metaEvalMul xPowBounds expFactorBounds
            -- Use expMulLogSub when both α and c are from the original expression
            -- (denote matches exactly; eval uses algebraic identity for speed)
            if αExprOpt.isSome && cExprOpt.isSome then
              let rexpr ← mkAppM ``RExpr.expMulLogSub #[αRExpr, xRExpr, cRExpr]
              return ← cacheReturn cache key (rexpr, bounds)
            -- Otherwise preserve original structure for rfl bridge
            let logR ← mkAppM ``RExpr.rlog #[xRExpr]
            let withSub ← match cExprOpt with
              | some _ => mkAppM ``RExpr.sub #[logR, cRExpr]
              | none => pure logR
            let withMul ← match αExprOpt with
              | some _ => mkAppM ``RExpr.mul #[αRExpr, withSub]
              | none => pure withSub
            let rexpr ← mkAppM ``RExpr.rexp #[withMul]
            return ← cacheReturn cache key (rexpr, bounds)
    -- Fallback: reify argument normally and compute expPoint bounds
    let (ra, ba) ← reifyToRExpr cache args[0]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.rexp #[ra]
    let elo := (Linglib.Interval.expPoint ba.lo).lo
    let ehi := (Linglib.Interval.expPoint ba.hi).hi
    return ← cacheReturn cache key (rexpr, ⟨elo, ehi⟩)

  -- Real.log
  if fn.isConstOf ``Real.log && args.size ≥ 1 then
    let (ra, ba) ← reifyToRExpr cache args[0]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.rlog #[ra]
    let bounds := if ba.lo > 0 then
                    ⟨(evalLogPoint ba.lo).1, (evalLogPoint ba.hi).2⟩
                  else ⟨-1000, 1000⟩
    return ← cacheReturn cache key (rexpr, bounds)

  -- If-then-else
  if fn.isConstOf ``ite && args.size ≥ 5 then
    let cond := args[1]!
    let thenBr := args[3]!
    let elseBr := args[4]!
    if cond.isAppOfArity ``Eq 3 then
      let cArgs := cond.getAppArgs
      let rhsC := cArgs[2]!
      if let some 0 := getOfNat? rhsC then
        let lhsC := cArgs[1]!
        let (rc, bc) ← reifyToRExpr cache lhsC (depth - 1)
        -- Always create iteZero to preserve expression structure for rfl bridge.
        -- Meta-level bounds determine which branch's bounds to use.
        let (rt, bt) ← reifyToRExpr cache thenBr (depth - 1)
        let (re, be) ← reifyToRExpr cache elseBr (depth - 1)
        let rexpr ← mkAppM ``RExpr.iteZero #[rc, rt, re]
        let bounds := if bc.lo > 0 then be
                      else if bc.lo == 0 && bc.hi == 0 then bt
                      else ⟨min bt.lo be.lo, max bt.hi be.hi⟩
        return ← cacheReturn cache key (rexpr, bounds)
      -- Bool condition: ite ((expr) = true) or ite ((expr) = false)
      -- Handles common RSA pattern `if (u == w.1) then ... else 0` which produces
      -- `ite ((u == w.1) = true) ...`. Cheap Bool whnf avoids expensive full-expr whnf.
      if cArgs[0]!.isConstOf ``Bool then
        let boolVal ← whnf cArgs[1]!
        let rhsVal ← whnf cArgs[2]!
        let lhsIsTrue := boolVal.isConstOf ``Bool.true
        let lhsIsFalse := boolVal.isConstOf ``Bool.false
        let rhsIsTrue := rhsVal.isConstOf ``Bool.true
        let rhsIsFalse := rhsVal.isConstOf ``Bool.false
        if (lhsIsTrue && rhsIsTrue) || (lhsIsFalse && rhsIsFalse) then
          return ← reifyToRExpr cache thenBr (depth - 1)
        else if (lhsIsTrue && rhsIsFalse) || (lhsIsFalse && rhsIsTrue) then
          return ← reifyToRExpr cache elseBr (depth - 1)
    let e' ← whnf e
    if !e.equal e' then
      return ← reifyToRExpr cache e' (depth - 1)
    throwError "rsa_predict: unsupported ite condition: {← ppExpr cond}"

  -- Decidable.rec (from whnf'd ite)
  if fn.isConstOf ``Decidable.rec && args.size ≥ 5 then
    let prop := args[0]!
    let isFalseBr := args[2]!
    let isTrueBr := args[3]!
    if prop.isAppOfArity ``Eq 3 then
      let propArgs := prop.getAppArgs
      let lhsC := propArgs[1]!
      let rhsC := propArgs[2]!
      if let some 0 := getOfNat? rhsC then
        let (rc, bc) ← reifyToRExpr cache lhsC (depth - 1)
        -- Always create iteZero to preserve expression structure for rfl bridge.
        let dummyTrueProof := mkApp2 (mkConst ``sorryAx [levelZero]) prop (toExpr true)
        let thenBody := (Expr.app isTrueBr dummyTrueProof).headBeta
        let negProp ← mkAppM ``Not #[prop]
        let dummyFalseProof := mkApp2 (mkConst ``sorryAx [levelZero]) negProp (toExpr true)
        let elseBody := (Expr.app isFalseBr dummyFalseProof).headBeta
        let (rt, bt) ← reifyToRExpr cache thenBody (depth - 1)
        let (re, be) ← reifyToRExpr cache elseBody (depth - 1)
        let rexpr ← mkAppM ``RExpr.iteZero #[rc, rt, re]
        let bounds := if bc.lo > 0 then be
                      else if bc.lo == 0 && bc.hi == 0 then bt
                      else ⟨min bt.lo be.lo, max bt.hi be.hi⟩
        return ← cacheReturn cache key (rexpr, bounds)

  -- Fast-path for summation forms
  let fnName := fn.constName?
  if fnName == some ``Finset.sum ||
     fnName == some ``Multiset.sum ||
     fnName == some ``Multiset.fold ||
     fnName == some ``List.foldr ||
     fnName == some ``List.foldl ||
     fnName == some ``List.sum ||
     fnName == some ``Quot.lift then
    let e' ← whnf e
    if !e.equal e' then
      return ← reifyToRExpr cache e' (depth - 1)

  -- Default: unfold one definition, headBeta
  if let some e' ← unfoldDefinition? e then
    return ← reifyToRExpr cache e'.headBeta (depth - 1)

  -- Reducible whnf: does iota (case splits) but stops at OfNat.ofNat
  -- This prevents whnf from reducing OfNat.ofNat ℝ n _ to the Cauchy form
  let eR ← withReducible do whnf e
  if !e.equal eR then
    return ← reifyToRExpr cache eR (depth - 1)

  -- Full whnf fallback
  let e' ← whnf e
  if !e.equal e' then
    return ← reifyToRExpr cache e' (depth - 1)

  -- Tertiary: detect numeric literals via isDefEq (small) or findEmbeddedNat (large)
  let eType ← inferType e
  if eType.isConstOf ``Real then
    -- Fast path: check Cauchy form before the isDefEq loop
    if e.getAppFn.isConstOf ``Real.ofCauchy then
      if let some q ← extractRatFromCauchy e then
        if q.den == 1 && q.num ≥ 0 then
          let n := q.num.toNat
          let rexpr ← mkAppM ``RExpr.nat #[mkRawNatLit n]
          return ← cacheReturn cache key (rexpr, ⟨n, n⟩)
        else
          let numE ← mkAppM ``RExpr.nat #[mkRawNatLit q.num.natAbs]
          let denE ← mkAppM ``RExpr.nat #[mkRawNatLit q.den]
          let divE ← mkAppM ``RExpr.div #[numE, denE]
          let rexpr ← if q.num < 0 then mkAppM ``RExpr.neg #[divE] else pure divE
          return ← cacheReturn cache key (rexpr, ⟨q, q⟩)
      if let some n := findEmbeddedNat e then
        let rexpr ← mkAppM ``RExpr.nat #[mkRawNatLit n]
        return ← cacheReturn cache key (rexpr, ⟨n, n⟩)
    for n in ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ) do
      let nE := mkRawNatLit n
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, nE, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e target catch _ => return false
      if isEq then
        let rexpr ← mkAppM ``RExpr.nat #[nE]
        return ← cacheReturn cache key (rexpr, ⟨n, n⟩)

  -- Quaternary: detect binary ops via isDefEq (catches internal forms like Real.add✝)
  if args.size ≥ 2 then
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    let isAdd ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HAdd.hAdd #[a, b]) catch _ => return false
    if isAdd then
      let (ra, ba) ← reifyToRExpr cache a (depth - 1)
      let (rb, bb) ← reifyToRExpr cache b (depth - 1)
      let rexpr ← mkAppM ``RExpr.add #[ra, rb]
      return ← cacheReturn cache key (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)
    let isMul ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HMul.hMul #[a, b]) catch _ => return false
    if isMul then
      let (ra, ba) ← reifyToRExpr cache a (depth - 1)
      let (rb, bb) ← reifyToRExpr cache b (depth - 1)
      let rexpr ← mkAppM ``RExpr.mul #[ra, rb]
      return ← cacheReturn cache key (rexpr, metaEvalMul ba bb)
    let isDiv ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HDiv.hDiv #[a, b]) catch _ => return false
    if isDiv then
      let (ra, ba) ← reifyToRExpr cache a (depth - 1)
      let (rb, bb) ← reifyToRExpr cache b (depth - 1)
      let rexpr ← mkAppM ``RExpr.div #[ra, rb]
      let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                    else ⟨-1, 1⟩
      return ← cacheReturn cache key (rexpr, bounds)

  -- Detect exp/log/inv/rpow via isDefEq (catches internal forms after whnf)
  if eType.isConstOf ``Real then
    let expMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Real.exp #[argM]) then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := expMatch then
      let (ra, ba) ← reifyToRExpr cache arg (depth - 1)
      let rexpr ← mkAppM ``RExpr.rexp #[ra]
      let elo := (Linglib.Interval.expPoint ba.lo).lo
      let ehi := (Linglib.Interval.expPoint ba.hi).hi
      return ← cacheReturn cache key (rexpr, ⟨elo, ehi⟩)
    let logMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Real.log #[argM]) then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := logMatch then
      let (ra, ba) ← reifyToRExpr cache arg (depth - 1)
      let rexpr ← mkAppM ``RExpr.rlog #[ra]
      let bounds := if ba.lo > 0 then
                      ⟨(evalLogPoint ba.lo).1, (evalLogPoint ba.hi).2⟩
                    else ⟨-1000, 1000⟩
      return ← cacheReturn cache key (rexpr, bounds)
    let invMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Inv.inv #[argM]) then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := invMatch then
      let (ra, ba) ← reifyToRExpr cache arg (depth - 1)
      let rexpr ← mkAppM ``RExpr.inv #[ra]
      let bounds := if ba.lo > 0 then ⟨1 / ba.hi, 1 / ba.lo⟩ else ⟨-1, 1⟩
      return ← cacheReturn cache key (rexpr, bounds)

  -- rpow via isDefEq
  if eType.isConstOf ``Real then
    let rpowMatch ← withNewMCtxDepth do
      try
        let baseM ← mkFreshExprMVar (mkConst ``Real)
        let expM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Real.rpow #[baseM, expM]) then
          return some (← instantiateMVars baseM, ← instantiateMVars expM)
        else return none
      catch _ => return none
    if let some (base, exp) := rpowMatch then
      if let some n ← resolveNat? exp then
        let (rb, bb) ← reifyToRExpr cache base (depth - 1)
        let rexpr ← mkAppM ``RExpr.rpow #[rb, mkRawNatLit n]
        let bounds := if n == 0 then ⟨1, 1⟩
                      else if bb.lo ≥ 0 then ⟨bb.lo ^ n, bb.hi ^ n⟩
                      else ⟨0, 1⟩
        return ← cacheReturn cache key (rexpr, bounds)

  throwError "rsa_predict: cannot reify: {← ppExpr e} (depth: {depth})"

-- ============================================================================
-- Extract ℚ from ℝ Expression
-- ============================================================================

/-- Check an expression for known arithmetic operator patterns. -/
private partial def matchArithOp (e : Expr) (extractRatFn : Expr → MetaM ℚ) :
    MetaM (Option ℚ) := do
  -- Natural literal
  if let some n := getNat? e then return some (n : ℚ)
  -- HDiv
  if isAppOfMin e ``HDiv.hDiv 6 then
    let num ← extractRatFn e.getAppArgs[4]!
    let den ← extractRatFn e.getAppArgs[5]!
    if den ≠ 0 then return some (num / den)
  if isAppOfMin e ``Div.div 4 then
    let num ← extractRatFn e.getAppArgs[2]!
    let den ← extractRatFn e.getAppArgs[3]!
    if den ≠ 0 then return some (num / den)
  -- HMul
  if isAppOfMin e ``HMul.hMul 6 then
    let a ← extractRatFn e.getAppArgs[4]!
    let b ← extractRatFn e.getAppArgs[5]!
    return some (a * b)
  if isAppOfMin e ``Mul.mul 4 then
    let a ← extractRatFn e.getAppArgs[2]!
    let b ← extractRatFn e.getAppArgs[3]!
    return some (a * b)
  -- HAdd
  if isAppOfMin e ``HAdd.hAdd 6 then
    let a ← extractRatFn e.getAppArgs[4]!
    let b ← extractRatFn e.getAppArgs[5]!
    return some (a + b)
  if isAppOfMin e ``Add.add 4 then
    let a ← extractRatFn e.getAppArgs[2]!
    let b ← extractRatFn e.getAppArgs[3]!
    return some (a + b)
  -- HSub
  if isAppOfMin e ``HSub.hSub 6 then
    let a ← extractRatFn e.getAppArgs[4]!
    let b ← extractRatFn e.getAppArgs[5]!
    return some (a - b)
  -- Neg
  if isAppOfMin e ``Neg.neg 3 then
    let a ← extractRatFn e.getAppArgs[2]!
    return some (-a)
  -- Inv (a⁻¹ = 1/a)
  if isAppOfMin e ``Inv.inv 3 then
    let a ← extractRatFn e.getAppArgs[2]!
    if a ≠ 0 then return some (1 / a)
  return none

/-- Try to extract a ℚ literal from an ℝ expression.
    Uses incremental unfolding to avoid whnf over-reducing operators. -/
partial def extractRat (e : Expr) : MetaM ℚ := do
  -- 1. Check original expression for operators/literals
  if let some q ← matchArithOp e extractRat then return q
  -- 2. Try incremental unfolding (preserves operator structure)
  if let some e' ← unfoldDefinition? e then
    let e'' := e'.headBeta
    if let some q ← matchArithOp e'' extractRat then return q
    return ← extractRat e''
  -- 3. Try whnf (for leaves like numeric literals)
  let e' ← whnf e
  if let some n := getNat? e' then return (n : ℚ)
  if let some q ← matchArithOp e' extractRat then return q
  -- 4. Detect ℝ literal — may be in Cauchy sequence form after whnf
  -- Extract ℚ from Cauchy form by evaluating the sequence at index 0
  let eType ← inferType e'
  if e'.getAppFn.isConstOf ``Real.ofCauchy then
    if let some q ← extractRatFromCauchy e' then return q
    if let some n := findEmbeddedNat e' then return (n : ℚ)
  if eType.isConstOf ``Real then
    -- Try isDefEq for small numbers (handles Real.one✝, Real.zero✝, etc.)
    for n in ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ) do
      let nE := mkRawNatLit n
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, nE, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e' target catch _ => return false
      if isEq then return (n : ℚ)
    -- Try scanning for embedded nat literal (handles large numbers like 4205)
    -- Only for Cauchy forms — not for internal ops like Real.mul which embed
    -- multiple nats (numerator AND denominator) and findEmbeddedNat would pick
    -- up only the first one.
    if e'.getAppFn.isConstOf ``Real.ofCauchy then
      if let some q ← extractRatFromCauchy e' then return q
      if let some n := findEmbeddedNat e' then return (n : ℚ)
  -- 5. isDefEq fallback for binary ops after whnf
  -- Handles internal names like Real.mul, Real.add that don't match HMul/HAdd
  let eType' ← if eType.isConstOf ``Real then pure eType else inferType e'
  if eType'.isConstOf ``Real then
    -- Binary ops
    if e'.getAppNumArgs ≥ 2 then
      let a := e'.getAppArgs[e'.getAppNumArgs - 2]!
      let b := e'.getAppArgs[e'.getAppNumArgs - 1]!
      let isMul ← withNewMCtxDepth do
        try isDefEq e' (← mkAppM ``HMul.hMul #[a, b]) catch _ => return false
      if isMul then
        let va ← extractRat a
        let vb ← extractRat b
        return va * vb
      let isAdd ← withNewMCtxDepth do
        try isDefEq e' (← mkAppM ``HAdd.hAdd #[a, b]) catch _ => return false
      if isAdd then
        let va ← extractRat a
        let vb ← extractRat b
        return va + vb
      let isDiv ← withNewMCtxDepth do
        try isDefEq e' (← mkAppM ``HDiv.hDiv #[a, b]) catch _ => return false
      if isDiv then
        let va ← extractRat a
        let vb ← extractRat b
        if vb ≠ 0 then return va / vb
      let isSub ← withNewMCtxDepth do
        try isDefEq e' (← mkAppM ``HSub.hSub #[a, b]) catch _ => return false
      if isSub then
        let va ← extractRat a
        let vb ← extractRat b
        return va - vb
    -- Unary ops (Inv.inv, Neg.neg)
    if e'.getAppNumArgs ≥ 1 then
      let a := e'.getAppArgs.back!
      let isInv ← withNewMCtxDepth do
        try isDefEq e' (← mkAppM ``Inv.inv #[a]) catch _ => return false
      if isInv then
        let va ← extractRat a
        if va ≠ 0 then return 1 / va
      let isNeg ← withNewMCtxDepth do
        try isDefEq e' (← mkAppM ``Neg.neg #[a]) catch _ => return false
      if isNeg then
        let va ← extractRat a
        return -va
  throwError "rsa_predict: cannot extract ℚ from: {← ppExpr e'}"

-- ============================================================================
-- S1 Score Reification Orchestrator
-- ============================================================================

/-- Shared infrastructure: extract config info, reify all S1 scores.
    Returns (U, W, L types, element arrays, s1Bounds, wpValues, lpValues). -/
def reifyS1Scores (cfg : Expr) :
    MetaM (Expr × Expr × Expr ×
           Array Expr × Array Expr × Array Expr ×
           Array MetaBounds × Array ℚ × Array ℚ) := do
  let cfgType ← whnf (← inferType cfg)
  let cfgArgs := cfgType.getAppArgs
  unless cfgArgs.size ≥ 2 do
    throwError "rsa_predict: cannot extract U, W from config type"
  let U := cfgArgs[0]!
  let W := cfgArgs[1]!
  let latentExpr ← mkAppM ``RSA.RSAConfig.Latent #[cfg]
  let L ← whnf latentExpr

  let (_, allUElems) ← getFiniteElems U
  let (_, allWElems) ← getFiniteElems W
  let (_, allLElems) ← getFiniteElems L

  logInfo m!"rsa_predict: |U| = {allUElems.size}, |W| = {allWElems.size}, |L| = {allLElems.size}"

  -- Extract worldPrior and latentPrior ℚ values
  let mut wpValues : Array ℚ := #[]
  for w in allWElems do
    let wpExpr ← mkAppM ``RSA.RSAConfig.worldPrior #[cfg, w]
    wpValues := wpValues.push (← extractRat wpExpr)

  -- latentPrior is now W → Latent → ℝ; extract as 2D array indexed [wIdx * nL + lIdx]
  let mut lpValues : Array ℚ := #[]
  for w in allWElems do
    for l in allLElems do
      let lpExpr ← mkAppM ``RSA.RSAConfig.latentPrior #[cfg, w, l]
      lpValues := lpValues.push (← extractRat lpExpr)

  -- Warm up cache: pre-compute all L0 values
  let reifyCache ← IO.mkRef (∅ : Std.HashMap UInt64 (Expr × MetaBounds))
  for l in allLElems do
    let l0agent ← mkAppM ``RSA.RSAConfig.L0agent #[cfg, l]
    for u in allUElems do
      for w in allWElems do
        let l0Expr ← mkAppM ``Core.RationalAction.policy #[l0agent, u, w]
        let _ ← reifyToRExpr reifyCache l0Expr maxDepth

  -- Reify S1 scores
  let mut s1Bounds : Array MetaBounds := #[]
  let total := allLElems.size * allWElems.size * allUElems.size
  logInfo m!"rsa_predict: reifying {total} S1 scores..."
  let mut count : ℕ := 0
  for l in allLElems do
    let s1agent ← mkAppM ``RSA.RSAConfig.S1agent #[cfg, l]
    for w in allWElems do
      for u in allUElems do
        let scoreExpr ← mkAppM ``Core.RationalAction.score #[s1agent, w, u]
        let (_, b) ← reifyToRExpr reifyCache scoreExpr maxDepth
        s1Bounds := s1Bounds.push b
        count := count + 1
        if count % 100 = 0 then
          logInfo m!"rsa_predict: ... {count}/{total} scores reified"

  let nonZero := s1Bounds.filter fun b => !(b.lo == 0 && b.hi == 0)
  logInfo m!"rsa_predict: {nonZero.size}/{total} non-zero S1 scores"

  return (U, W, L, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues)

end Linglib.Tactics.RSAPredict
