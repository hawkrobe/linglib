import Lean
import Linglib.Theories.Pragmatics.RSA.Core.Verified
import Linglib.Core.Interval.ReflectInterval

set_option autoImplicit false

/-!
# RSAPredict — Level-Aware Verified RSA Predictions

The `rsa_predict` tactic proves ℝ comparison goals on RSA models by:

1. Pattern-matching the goal to find the RSA config, utterance, and worlds
2. Pre-computing each S1 score individually via RExpr reification (bounded per element)
3. Composing L1 scores using generic evaluators from `RSA.Verified`
4. Delegating the final comparison to `native_decide`

Unlike `rsa_decide` (which reifies the entire L1 expression as one giant term),
`rsa_predict` reifies S1 scores one at a time. This prevents exponential blowup
on nested models (L0→S1→L1) like Kao et al. (2014).

## Usage

```lean
theorem prediction : cfg.L1 u w₁ > cfg.L1 u w₂ := by rsa_predict
```
-/

namespace Linglib.Tactics

open Lean Meta Elab Tactic
open Linglib.Interval

-- ============================================================================
-- Expr Inspection Helpers (shared with RSADecide)
-- ============================================================================

/-- Extract a natural number from `@OfNat.ofNat T n inst`. -/
private def getOfNat?' (e : Expr) : Option ℕ := do
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  e.appFn!.appArg!.rawNatLit?

/-- Extract a natural number from `@Nat.cast T inst n`. -/
private def getNatCast?' (e : Expr) : Option ℕ := do
  guard (e.isAppOfArity ``Nat.cast 3)
  e.getAppArgs[2]!.rawNatLit?

private def getNat?' (e : Expr) : Option ℕ :=
  getOfNat?' e <|> getNatCast?' e

private def isAppOfMin' (e : Expr) (name : Name) (minArgs : ℕ) : Bool :=
  e.getAppFn.isConstOf name && e.getAppNumArgs ≥ minArgs

/-- Try to extract a natural number, unfolding/reducing as needed. -/
private def resolveNat?' (e : Expr) : MetaM (Option ℕ) := do
  if let some n := getNat?' e then return some n
  let e' ← whnf e
  if let some n := getNat?' e' then return some n
  if e'.isAppOfArity ``Nat.cast 3 then
    let inner ← whnf e'.getAppArgs[2]!
    return inner.rawNatLit?
  let eType ← inferType e'
  if eType.isConstOf ``Real then
    for n in ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ) do
      let nE := mkRawNatLit n
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, nE, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e' target catch _ => return false
      if isEq then return some n
  return none

-- ============================================================================
-- Simplified RExpr Reifier
-- ============================================================================

/-- Meta-level interval bounds for early checks. -/
private structure MetaBounds where
  lo : ℚ
  hi : ℚ
  deriving Inhabited

private def metaEvalMul' (a b : MetaBounds) : MetaBounds :=
  if a.lo == 0 && a.hi == 0 then ⟨0, 0⟩
  else if b.lo == 0 && b.hi == 0 then ⟨0, 0⟩
  else if a.lo ≥ 0 && b.lo ≥ 0 then ⟨a.lo * b.lo, a.hi * b.hi⟩
  else
    let c00 := a.lo * b.lo; let c01 := a.lo * b.hi
    let c10 := a.hi * b.lo; let c11 := a.hi * b.hi
    ⟨min (min c00 c01) (min c10 c11), max (max c00 c01) (max c10 c11)⟩

private def evalLogPoint' (q : ℚ) : ℚ × ℚ :=
  if h : 0 < q then
    let I := Linglib.Interval.logPoint q h
    (I.lo, I.hi)
  else (0, 0)

/-- Scan an expression for an embedded raw natural number literal.
    After whnf reduces `n : ℝ` to its Cauchy sequence form, the natural
    number is typically buried inside `@Nat.cast ℚ _ n` or similar.
    This scans the expression tree (limited depth) for the first raw nat literal. -/
private partial def findEmbeddedNat (e : Expr) (depth : ℕ := 15) : Option ℕ :=
  if depth == 0 then none
  else if let some n := e.rawNatLit? then some n
  else e.getAppArgs.findSome? (findEmbeddedNat · (depth - 1))

private def maxDepth : ℕ := 200

/-- Simplified RExpr reifier for rsa_predict.
    Produces RExpr values + meta-level bounds. -/
private partial def reifyToRExpr (e : Expr) (depth : ℕ) : MetaM (Expr × MetaBounds) := do
  if depth == 0 then
    throwError "rsa_predict: max reification depth on: {← ppExpr e}"

  -- Let binding: substitute
  if e.isLet then
    return ← reifyToRExpr (e.letBody!.instantiate1 e.letValue!) (depth - 1)

  -- Natural literal
  if let some n := getOfNat?' e then
    let rexpr ← mkAppM ``RExpr.nat #[mkRawNatLit n]
    return (rexpr, ⟨n, n⟩)

  let fn := e.getAppFn
  let args := e.getAppArgs

  -- Addition: @HAdd.hAdd ℝ ℝ ℝ _ a b
  if isAppOfMin' e ``HAdd.hAdd 6 then
    let (ra, ba) ← reifyToRExpr args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.add #[ra, rb]
    return (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)

  if isAppOfMin' e ``Add.add 4 then
    let (ra, ba) ← reifyToRExpr args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.add #[ra, rb]
    return (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)

  -- Multiplication
  if isAppOfMin' e ``HMul.hMul 6 then
    let (ra, ba) ← reifyToRExpr args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.mul #[ra, rb]
    let m := metaEvalMul' ba bb
    return (rexpr, m)

  if isAppOfMin' e ``Mul.mul 4 then
    let (ra, ba) ← reifyToRExpr args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.mul #[ra, rb]
    let m := metaEvalMul' ba bb
    return (rexpr, m)

  -- Division
  if isAppOfMin' e ``HDiv.hDiv 6 then
    let (ra, ba) ← reifyToRExpr args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.div #[ra, rb]
    let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                  else ⟨-1, 1⟩
    return (rexpr, bounds)

  if isAppOfMin' e ``Div.div 4 then
    let (ra, ba) ← reifyToRExpr args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.div #[ra, rb]
    let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                  else ⟨-1, 1⟩
    return (rexpr, bounds)

  -- Negation
  if isAppOfMin' e ``Neg.neg 3 then
    let (ra, ba) ← reifyToRExpr args[2]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.neg #[ra]
    return (rexpr, ⟨-ba.hi, -ba.lo⟩)

  -- Subtraction
  if isAppOfMin' e ``HSub.hSub 6 then
    let (ra, ba) ← reifyToRExpr args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.sub #[ra, rb]
    return (rexpr, ⟨ba.lo - bb.hi, ba.hi - bb.lo⟩)

  if isAppOfMin' e ``Sub.sub 4 then
    let (ra, ba) ← reifyToRExpr args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.sub #[ra, rb]
    return (rexpr, ⟨ba.lo - bb.hi, ba.hi - bb.lo⟩)

  -- Real.rpow
  if fn.isConstOf ``Real.rpow && args.size ≥ 2 then
    if let some n ← resolveNat?' args[1]! then
      let (rb, bb) ← reifyToRExpr args[0]! (depth - 1)
      let rexpr ← mkAppM ``RExpr.rpow #[rb, mkRawNatLit n]
      let bounds := if n == 0 then ⟨1, 1⟩
                    else if bb.lo ≥ 0 then ⟨bb.lo ^ n, bb.hi ^ n⟩
                    else ⟨0, 1⟩
      return (rexpr, bounds)
    if let some e' ← unfoldDefinition? e then
      return ← reifyToRExpr e' (depth - 1)

  -- Real.exp
  if fn.isConstOf ``Real.exp && args.size ≥ 1 then
    let (ra, ba) ← reifyToRExpr args[0]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.rexp #[ra]
    let elo := (Linglib.Interval.expPoint ba.lo).lo
    let ehi := (Linglib.Interval.expPoint ba.hi).hi
    return (rexpr, ⟨elo, ehi⟩)

  -- Real.log
  if fn.isConstOf ``Real.log && args.size ≥ 1 then
    let (ra, ba) ← reifyToRExpr args[0]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.rlog #[ra]
    let bounds := if ba.lo > 0 then
                    ⟨(evalLogPoint' ba.lo).1, (evalLogPoint' ba.hi).2⟩
                  else ⟨-1000, 1000⟩
    return (rexpr, bounds)

  -- If-then-else
  if fn.isConstOf ``ite && args.size ≥ 5 then
    let cond := args[1]!
    let thenBr := args[3]!
    let elseBr := args[4]!
    if cond.isAppOfArity ``Eq 3 then
      let cArgs := cond.getAppArgs
      let rhsC := cArgs[2]!
      if let some 0 := getOfNat?' rhsC then
        let lhsC := cArgs[1]!
        let (rc, bc) ← reifyToRExpr lhsC (depth - 1)
        if bc.lo > 0 then
          let (re, be) ← reifyToRExpr elseBr (depth - 1)
          let rexpr ← mkAppM ``RExpr.iteZero #[rc, ← mkAppM ``RExpr.nat #[mkRawNatLit 0], re]
          return (rexpr, be)
        else if bc.lo == 0 && bc.hi == 0 then
          let (rt, bt) ← reifyToRExpr thenBr (depth - 1)
          let rexpr ← mkAppM ``RExpr.iteZero #[rc, rt, ← mkAppM ``RExpr.nat #[mkRawNatLit 0]]
          return (rexpr, bt)
    let e' ← whnf e
    if !e.equal e' then
      return ← reifyToRExpr e' (depth - 1)
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
      if let some 0 := getOfNat?' rhsC then
        let (rc, bc) ← reifyToRExpr lhsC (depth - 1)
        if bc.lo > 0 then
          let negProp ← mkAppM ``Not #[prop]
          let dummyProof := mkApp2 (mkConst ``sorryAx [levelZero]) negProp (toExpr true)
          let elseBody := (Expr.app isFalseBr dummyProof).headBeta
          let (re, be) ← reifyToRExpr elseBody (depth - 1)
          let rexpr ← mkAppM ``RExpr.iteZero #[rc, ← mkAppM ``RExpr.nat #[mkRawNatLit 0], re]
          return (rexpr, be)
        else if bc.lo == 0 && bc.hi == 0 then
          let dummyProof := mkApp2 (mkConst ``sorryAx [levelZero]) prop (toExpr true)
          let thenBody := (Expr.app isTrueBr dummyProof).headBeta
          let (rt, bt) ← reifyToRExpr thenBody (depth - 1)
          let rexpr ← mkAppM ``RExpr.iteZero #[rc, rt, ← mkAppM ``RExpr.nat #[mkRawNatLit 0]]
          return (rexpr, bt)

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
      return ← reifyToRExpr e' (depth - 1)

  -- Default: unfold one definition, headBeta
  if let some e' ← unfoldDefinition? e then
    return ← reifyToRExpr e'.headBeta (depth - 1)

  -- Reducible whnf: does iota (case splits) but stops at OfNat.ofNat
  -- This prevents whnf from reducing OfNat.ofNat ℝ n _ to the Cauchy form
  let eR ← withReducible do whnf e
  if !e.equal eR then
    return ← reifyToRExpr eR (depth - 1)

  -- Full whnf fallback
  let e' ← whnf e
  if !e.equal e' then
    return ← reifyToRExpr e' (depth - 1)

  -- Tertiary: detect numeric literals via isDefEq (small) or findEmbeddedNat (large)
  let eType ← inferType e
  if eType.isConstOf ``Real then
    for n in ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ) do
      let nE := mkRawNatLit n
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, nE, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e target catch _ => return false
      if isEq then
        let rexpr ← mkAppM ``RExpr.nat #[nE]
        return (rexpr, ⟨n, n⟩)

  -- Quaternary: detect binary ops via isDefEq
  if args.size ≥ 2 then
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    let isAdd ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HAdd.hAdd #[a, b]) catch _ => return false
    if isAdd then
      let (ra, ba) ← reifyToRExpr a (depth - 1)
      let (rb, bb) ← reifyToRExpr b (depth - 1)
      let rexpr ← mkAppM ``RExpr.add #[ra, rb]
      return (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)
    let isMul ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HMul.hMul #[a, b]) catch _ => return false
    if isMul then
      let (ra, ba) ← reifyToRExpr a (depth - 1)
      let (rb, bb) ← reifyToRExpr b (depth - 1)
      let rexpr ← mkAppM ``RExpr.mul #[ra, rb]
      return (rexpr, metaEvalMul' ba bb)
    let isDiv ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HDiv.hDiv #[a, b]) catch _ => return false
    if isDiv then
      let (ra, ba) ← reifyToRExpr a (depth - 1)
      let (rb, bb) ← reifyToRExpr b (depth - 1)
      let rexpr ← mkAppM ``RExpr.div #[ra, rb]
      let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                    else ⟨-1, 1⟩
      return (rexpr, bounds)

  -- Detect exp/log via isDefEq
  if eType.isConstOf ``Real then
    let expMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Real.exp #[argM]) then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := expMatch then
      let (ra, ba) ← reifyToRExpr arg (depth - 1)
      let rexpr ← mkAppM ``RExpr.rexp #[ra]
      let elo := (Linglib.Interval.expPoint ba.lo).lo
      let ehi := (Linglib.Interval.expPoint ba.hi).hi
      return (rexpr, ⟨elo, ehi⟩)
    let logMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Real.log #[argM]) then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := logMatch then
      let (ra, ba) ← reifyToRExpr arg (depth - 1)
      let rexpr ← mkAppM ``RExpr.rlog #[ra]
      let bounds := if ba.lo > 0 then
                      ⟨(evalLogPoint' ba.lo).1, (evalLogPoint' ba.hi).2⟩
                    else ⟨-1000, 1000⟩
      return (rexpr, bounds)
    let invMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Inv.inv #[argM]) then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := invMatch then
      let (ra, ba) ← reifyToRExpr arg (depth - 1)
      let rexpr ← mkAppM ``RExpr.inv #[ra]
      let bounds := if ba.lo > 0 then ⟨1 / ba.hi, 1 / ba.lo⟩ else ⟨-1, 1⟩
      return (rexpr, bounds)

  -- Detect exp/log/inv/rpow via isDefEq (handles internal forms after whnf)
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
      if let some n ← resolveNat?' exp then
        let (rb, bb) ← reifyToRExpr base (depth - 1)
        let rexpr ← mkAppM ``RExpr.rpow #[rb, mkRawNatLit n]
        let bounds := if n == 0 then ⟨1, 1⟩
                      else if bb.lo ≥ 0 then ⟨bb.lo ^ n, bb.hi ^ n⟩
                      else ⟨0, 1⟩
        return (rexpr, bounds)

  throwError "rsa_predict: cannot reify: {← ppExpr e}"

-- ============================================================================
-- Enum Extraction
-- ============================================================================

/-- Extract a concrete List from a Lean Expr, extracting cons cells. -/
private def extractList (e : Expr) : MetaM (Array Expr) := do
  let mut elems : Array Expr := #[]
  let mut current ← whnf e
  for _ in List.range 1000 do
    if current.isAppOfArity ``List.cons 3 then
      elems := elems.push current.getAppArgs[1]!
      current ← whnf current.getAppArgs[2]!
    else
      break
  return elems

/-- Get all elements of a finite type as a List, represented as Lean Exprs.
    Returns (listExpr, elemExprs) where listExpr : Expr of type `List T`
    and elemExprs are the individual elements. -/
private partial def getFiniteElems (T : Expr) : MetaM (Expr × Array Expr) := do
  let T' ← whnf T
  -- Handle product types: A × B → cross product of elems
  if T'.isAppOfArity ``Prod 2 then
    let A := T'.getAppArgs[0]!
    let B := T'.getAppArgs[1]!
    let (_, elemsA) ← getFiniteElems A
    let (_, elemsB) ← getFiniteElems B
    let mut elems : Array Expr := #[]
    for a in elemsA do
      for b in elemsB do
        let pair ← mkAppM ``Prod.mk #[a, b]
        elems := elems.push pair
    let listExpr ← mkListLit T elems.toList
    return (listExpr, elems)
  -- Try: enumerate constructors of an inductive type (enum with no fields)
  if let .const name _ := T'.getAppFn then
    if let some info := (← getEnv).find? name then
      if let .inductInfo iv := info then
        let env ← getEnv
        let allNullary := iv.ctors.all fun c =>
          match env.find? c with
          | some (.ctorInfo ci) => ci.numParams + ci.numFields == iv.numParams
          | _ => false
        if allNullary then
          let tArgs := T'.getAppArgs
          let levels := if let .const _ ls := T'.getAppFn then ls else []
          let elems := iv.ctors.toArray.map fun c =>
            mkAppN (mkConst c levels) tArgs
          let listExpr ← mkListLit T elems.toList
          return (listExpr, elems)
  -- Fallback: try Finset.univ.toList with aggressive reduction
  let univExpr ← mkAppOptM ``Finset.univ #[T, none]
  let toListExpr ← mkAppM ``Finset.toList #[univExpr]
  let listReduced ← reduce toListExpr
  let elems ← extractList listReduced
  if elems.size > 0 then
    return (listReduced, elems)
  throwError "rsa_predict: cannot enumerate elements of type {← ppExpr T}"

-- ============================================================================
-- Extract ℚ from ℝ Expression
-- ============================================================================

/-- Check an expression for known arithmetic operator patterns. -/
private partial def matchArithOp (e : Expr) (extractRat : Expr → MetaM ℚ) :
    MetaM (Option ℚ) := do
  -- Natural literal
  if let some n := getNat?' e then return some (n : ℚ)
  -- HDiv
  if isAppOfMin' e ``HDiv.hDiv 6 then
    let num ← extractRat e.getAppArgs[4]!
    let den ← extractRat e.getAppArgs[5]!
    if den ≠ 0 then return some (num / den)
  if isAppOfMin' e ``Div.div 4 then
    let num ← extractRat e.getAppArgs[2]!
    let den ← extractRat e.getAppArgs[3]!
    if den ≠ 0 then return some (num / den)
  -- HMul
  if isAppOfMin' e ``HMul.hMul 6 then
    let a ← extractRat e.getAppArgs[4]!
    let b ← extractRat e.getAppArgs[5]!
    return some (a * b)
  if isAppOfMin' e ``Mul.mul 4 then
    let a ← extractRat e.getAppArgs[2]!
    let b ← extractRat e.getAppArgs[3]!
    return some (a * b)
  -- HAdd
  if isAppOfMin' e ``HAdd.hAdd 6 then
    let a ← extractRat e.getAppArgs[4]!
    let b ← extractRat e.getAppArgs[5]!
    return some (a + b)
  if isAppOfMin' e ``Add.add 4 then
    let a ← extractRat e.getAppArgs[2]!
    let b ← extractRat e.getAppArgs[3]!
    return some (a + b)
  -- HSub
  if isAppOfMin' e ``HSub.hSub 6 then
    let a ← extractRat e.getAppArgs[4]!
    let b ← extractRat e.getAppArgs[5]!
    return some (a - b)
  -- Neg
  if isAppOfMin' e ``Neg.neg 3 then
    let a ← extractRat e.getAppArgs[2]!
    return some (-a)
  return none

/-- Try to extract a ℚ literal from an ℝ expression.
    Uses incremental unfolding to avoid whnf over-reducing operators. -/
private partial def extractRat (e : Expr) : MetaM ℚ := do
  -- 1. Check original expression for operators/literals
  if let some q ← matchArithOp e extractRat then return q
  -- 2. Try incremental unfolding (preserves operator structure)
  if let some e' ← unfoldDefinition? e then
    let e'' := e'.headBeta
    if let some q ← matchArithOp e'' extractRat then return q
    return ← extractRat e''
  -- 3. Try whnf (for leaves like numeric literals)
  let e' ← whnf e
  if let some n := getNat?' e' then return (n : ℚ)
  if let some q ← matchArithOp e' extractRat then return q
  -- 4. Detect ℝ literal — may be in Cauchy sequence form after whnf
  let eType ← inferType e'
  if eType.isConstOf ``Real then
    -- Try isDefEq for small numbers (handles Real.one✝, Real.zero✝, etc.)
    for n in ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ) do
      let nE := mkRawNatLit n
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, nE, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e' target catch _ => return false
      if isEq then return (n : ℚ)
    -- Try scanning for embedded nat literal (handles large numbers like 4205)
    if let some n := findEmbeddedNat e' then return (n : ℚ)
  -- 5. isDefEq fallback for binary ops after whnf
  if eType.isConstOf ``Real && e'.getAppNumArgs ≥ 2 then
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
  throwError "rsa_predict: cannot extract ℚ from: {← ppExpr e'}"

-- ============================================================================
-- Build QInterval.exact Expr from ℚ
-- ============================================================================

/-- Build a Lean Expr for a ℚ literal. -/
private def mkRatExpr (q : ℚ) : MetaM Expr := do
  if q.den == 1 then
    -- Integer: just use Nat.cast or neg
    if q.num ≥ 0 then
      mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.num.natAbs]
    else
      mkAppM ``Neg.neg #[← mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.num.natAbs]]
  else
    -- Fraction: num / den
    let numExpr ← if q.num ≥ 0 then
      mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.num.natAbs]
    else
      mkAppM ``Neg.neg #[← mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.num.natAbs]]
    let denExpr ← mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.den]
    mkAppM ``HDiv.hDiv #[numExpr, denExpr]

/-- Build `QInterval.exact q` as a Lean Expr. -/
private def mkQIExact (q : ℚ) : MetaM Expr := do
  mkAppM ``QInterval.exact #[← mkRatExpr q]

-- ============================================================================
-- Build Match Expression
-- ============================================================================

-- ============================================================================
-- Core: Build S1 Score Table
-- ============================================================================

/-- Build an ite-chain function `fun (x : T) => if x == v₁ then r₁ else if x == v₂ then r₂ ...`
    using proper local variable binding. -/
private def buildIteFn (T : Expr) (entries : Array (Expr × Expr))
    (default : Expr) (name : Name := `x) : MetaM Expr := do
  withLocalDeclD name T fun x => do
    let mut body := default
    for i in (List.range entries.size).reverse do
      let (key, val) := entries[i]!
      let cond ← mkAppM ``BEq.beq #[x, key]
      body ← mkAppM ``cond #[cond, val, body]
    mkLambdaFVars #[x] body

/-- For each (l, w, u), reify the S1 score `(cfg.S1agent l).score w u`
    into an RExpr, then build a lookup function returning `RExpr.eval (...)`. -/
private def buildS1ScoreTable (cfg : Expr) (U W L : Expr)
    (allL : Array Expr) (allW : Array Expr) (allU : Array Expr) :
    MetaM (Expr × Array (Expr × Expr × Expr × MetaBounds)) := do
  let mut entries : Array (Expr × Expr × Expr × Expr × MetaBounds) := (#[] : Array _)
  let total := allL.size * allW.size * allU.size
  logInfo m!"rsa_predict: reifying {total} S1 scores..."
  for l in allL do
    let s1agent ← mkAppM ``RSA.RSAConfig.S1agent #[cfg, l]
    for w in allW do
      for u in allU do
        let scoreExpr ← mkAppM ``Core.RationalAction.score #[s1agent, w, u]
        let (rexpr, bounds) ← reifyToRExpr scoreExpr maxDepth
        entries := entries.push (l, w, u, rexpr, bounds)
  -- Build the function L → W → U → QInterval using nested lambdas
  let defaultVal ← mkAppM ``RExpr.eval #[← mkAppM ``RExpr.nat #[mkRawNatLit 0]]
  let fn ← withLocalDeclD `l L fun lVar => do
    withLocalDeclD `w W fun wVar => do
      withLocalDeclD `u U fun uVar => do
        let mut body := defaultVal
        for i in (List.range entries.size).reverse do
          let (li, wi, ui, rexpri, _) := entries[i]!
          let evali ← mkAppM ``RExpr.eval #[rexpri]
          let condL ← mkAppM ``BEq.beq #[lVar, li]
          let condW ← mkAppM ``BEq.beq #[wVar, wi]
          let condU ← mkAppM ``BEq.beq #[uVar, ui]
          let condLW ← mkAppM ``and #[condL, condW]
          let condAll ← mkAppM ``and #[condLW, condU]
          body ← mkAppM ``cond #[condAll, evali, body]
        mkLambdaFVars #[lVar, wVar, uVar] body
  let boundsInfo := entries.map fun (l, w, u, _, b) => (l, w, u, b)
  return (fn, boundsInfo)

-- ============================================================================
-- Goal Parsing
-- ============================================================================

/-- Try to unfold an expression to `RationalAction.policy ra s a`. -/
private def unfoldToPolicy (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut current := e
  for _ in List.range 10 do
    let fn := current.getAppFn
    let args := current.getAppArgs
    if fn.isConstOf ``Core.RationalAction.policy && args.size ≥ 6 then
      return some (args[3]!, args[4]!, args[5]!)  -- ra, s, a
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none

/-- Extract RSA config and arguments from a policy expression.
    Returns (cfg, u, w) where the expression is `cfg.L1 u w`. -/
private def parseL1Policy (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  -- Try to unfold to cfg.L1agent.policy u w
  if let some (ra, u, w) := ← unfoldToPolicy e then
    -- Check if ra is cfg.L1agent
    let mut raC := ra
    for _ in List.range 5 do
      let fn := raC.getAppFn
      let args := raC.getAppArgs
      if fn.isConstOf ``RSA.RSAConfig.L1agent && args.size ≥ 5 then
        let cfg := args[4]!
        return some (cfg, u, w)
      if let some ra' ← unfoldDefinition? raC then
        raC := ra'.headBeta
      else break
  return none

-- ============================================================================
-- Main Tactic
-- ============================================================================

/-- `rsa_predict` proves RSA prediction goals by level-aware interval arithmetic.

    Given a goal like `cfg.L1 u w₁ > cfg.L1 u w₂`, it:
    1. Extracts the config and arguments
    2. Pre-computes S1 scores individually via RExpr reification
    3. Composes L1 scores using generic evaluators
    4. Proves separation via `native_decide` -/
elab "rsa_predict" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Try native_decide first (handles ℚ, Bool, finite types)
  try
    evalTactic (← `(tactic| native_decide))
    return
  catch _ => pure ()

  let fn := goalType.getAppFn
  let args := goalType.getAppArgs

  -- GT.gt: lhs > rhs
  unless fn.isConstOf ``GT.gt && args.size ≥ 4 do
    throwError "rsa_predict: expected goal of the form `_ > _`, got: {← ppExpr goalType}"

  let lhs := args[2]!
  let rhs := args[3]!

  -- Parse both sides as L1 policies
  let some (cfg, u, w₁) ← parseL1Policy lhs |
    throwError "rsa_predict: cannot parse LHS as cfg.L1 u w"
  let some (cfg₂, _u₂, w₂) ← parseL1Policy rhs |
    throwError "rsa_predict: cannot parse RHS as cfg.L1 u w"

  -- Verify same config
  unless ← isDefEq cfg cfg₂ do
    throwError "rsa_predict: LHS and RHS use different configs"

  logInfo m!"rsa_predict: parsed goal as L1 comparison"

  -- Get types U, W, and Latent
  let cfgType ← inferType cfg
  let cfgType ← whnf cfgType
  let cfgArgs := cfgType.getAppArgs
  logInfo m!"rsa_predict: config type = {← ppExpr cfgType}, #args = {cfgArgs.size}"
  unless cfgArgs.size ≥ 2 do
    throwError "rsa_predict: cannot extract U, W from config type: {← ppExpr cfgType}"
  let U := cfgArgs[0]!
  let W := cfgArgs[1]!
  -- Get Latent type
  let latentExpr ← mkAppM ``RSA.RSAConfig.Latent #[cfg]
  let L ← whnf latentExpr

  logInfo m!"rsa_predict: U = {← ppExpr U}, W = {← ppExpr W}, Latent = {← ppExpr L}"

  -- Get enum lists
  let (allUList, allUElems) ← getFiniteElems U
  let (_, allWElems) ← getFiniteElems W
  let (allLList, allLElems) ← getFiniteElems L

  logInfo m!"rsa_predict: |U| = {allUElems.size}, |W| = {allWElems.size}, |L| = {allLElems.size}"

  -- Build worldPrior_qi table
  let mut wpEntries : Array (Expr × Expr) := #[]
  for w in allWElems do
    let wpExpr ← mkAppM ``RSA.RSAConfig.worldPrior #[cfg, w]
    let wpVal ← extractRat wpExpr
    let qiExpr ← mkQIExact wpVal
    wpEntries := wpEntries.push (w, qiExpr)

  -- Build latentPrior_qi table
  let mut lpEntries : Array (Expr × Expr) := #[]
  for l in allLElems do
    let lpExpr ← mkAppM ``RSA.RSAConfig.latentPrior #[cfg, l]
    let lpVal ← extractRat lpExpr
    let qiExpr ← mkQIExact lpVal
    lpEntries := lpEntries.push (l, qiExpr)

  logInfo m!"rsa_predict: extracted worldPrior and latentPrior tables"

  -- Build S1 score table
  let (s1ScoreFn, _s1Bounds) ← buildS1ScoreTable cfg U W L allLElems allWElems allUElems

  logInfo m!"rsa_predict: S1 score table built, applying bridge theorem..."

  -- Determine which bridge theorem to use
  let isLatent := allLElems.size > 1 || !(← isDefEq L (mkConst ``Unit))

  if isLatent then
    -- Build worldPrior_qi and latentPrior_qi functions
    let defaultQI ← mkQIExact 0
    let wpFn ← buildIteFn W wpEntries defaultQI `w
    let lpFn ← buildIteFn L lpEntries defaultQI `l

    -- Apply L1_latent_gt_of_score_sep
    -- The separation hypothesis is: (L1_latent_score_qi ... w₂).hi < (L1_latent_score_qi ... w₁).lo
    let score_w1 ← mkAppM ``RSA.Verified.L1_latent_score_qi
      #[allUList, allLList, s1ScoreFn, wpFn, lpFn, u, w₁]
    let score_w2 ← mkAppM ``RSA.Verified.L1_latent_score_qi
      #[allUList, allLList, s1ScoreFn, wpFn, lpFn, u, w₂]
    let sepType ← mkAppM ``LT.lt
      #[← mkAppM ``QInterval.hi #[score_w2],
        ← mkAppM ``QInterval.lo #[score_w1]]

    -- Create separation proof via native_decide
    let sepMVar ← mkFreshExprMVar sepType
    let savedGoals ← getGoals
    setGoals [sepMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      setGoals savedGoals
      throwError "rsa_predict: native_decide failed on separation check: {e.toMessageData}"
    setGoals savedGoals

    -- Build full proof
    let proof ← mkAppM ``RSA.Verified.L1_latent_gt_of_score_sep
      #[allUList, allLList, s1ScoreFn, wpFn, lpFn, cfg, u, w₁, w₂, sepMVar]

    -- Assign proof to goal
    let proofType ← inferType proof
    let goalType' ← goal.getType
    if ← isDefEq proofType goalType' then
      goal.assign proof
    else
      -- Bridge cast mismatch
      let goalWithH ← goal.assert `h_rsa proofType proof
      let (_, finalGoal) ← goalWithH.intro1
      setGoals [finalGoal]
      try evalTactic (← `(tactic| assumption_mod_cast))
      catch _ =>
        try evalTactic (← `(tactic| push_cast at *; assumption))
        catch _ => evalTactic (← `(tactic| norm_cast at *; assumption))

    logInfo m!"rsa_predict: ✓ proved via L1_latent_gt_of_score_sep"

  else
    -- Vanilla (no latent variables): use L1_gt_of_score_sep
    -- S1_score for vanilla is W → U → QInterval (no latent dimension)
    -- Build from s1ScoreFn by applying the unit value
    let unitVal := mkConst ``Unit.unit
    -- Apply l = () directly
    let s1VanillaFn := (mkApp s1ScoreFn unitVal).headBeta

    -- Build worldPrior_qi function
    let defaultQI ← mkQIExact 0
    let wpFn ← buildIteFn W wpEntries defaultQI `w

    let score_w1 ← mkAppM ``RSA.Verified.L1_score_qi
      #[allUList, s1VanillaFn, wpFn, u, w₁]
    let score_w2 ← mkAppM ``RSA.Verified.L1_score_qi
      #[allUList, s1VanillaFn, wpFn, u, w₂]
    let sepType ← mkAppM ``LT.lt
      #[← mkAppM ``QInterval.hi #[score_w2],
        ← mkAppM ``QInterval.lo #[score_w1]]

    let sepMVar ← mkFreshExprMVar sepType
    let savedGoals ← getGoals
    setGoals [sepMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      setGoals savedGoals
      throwError "rsa_predict: native_decide failed on separation check: {e.toMessageData}"
    setGoals savedGoals

    let proof ← mkAppM ``RSA.Verified.L1_gt_of_score_sep
      #[allUList, s1VanillaFn, wpFn, cfg, u, w₁, w₂, sepMVar]

    let proofType ← inferType proof
    let goalType' ← goal.getType
    if ← isDefEq proofType goalType' then
      goal.assign proof
    else
      let goalWithH ← goal.assert `h_rsa proofType proof
      let (_, finalGoal) ← goalWithH.intro1
      setGoals [finalGoal]
      try evalTactic (← `(tactic| assumption_mod_cast))
      catch _ =>
        try evalTactic (← `(tactic| push_cast at *; assumption))
        catch _ => evalTactic (← `(tactic| norm_cast at *; assumption))

    logInfo m!"rsa_predict: ✓ proved via L1_gt_of_score_sep"

end Linglib.Tactics
