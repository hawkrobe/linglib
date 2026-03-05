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

/-- Try to extract ℚ from a `Rat`-typed expression that may involve opaque
    arithmetic operations (`Rat.mul`, `Rat.inv`, etc.). These are `@[extern]`
    in Lean 4 and don't reduce under `whnf`/`reduce`, so we recursively
    decompose arithmetic operators and evaluate at the meta level.

    Handles: `Rat.mul`, `Rat.inv`, `Rat.add`, `Rat.sub`, `Rat.neg`, `Rat.div`,
    `Rat.ofScientific`, `OfNat.ofNat`, `Rat.mk'` constructor, and
    `Rat.num`/`Rat.den` projections. -/
partial def extractRatQ (e : Expr) : MetaM (Option ℚ) := do
  let e' ← whnf e
  let fn := e'.getAppFn
  let args := e'.getAppArgs
  -- Rat.mk' constructor: Rat.mk' num den ...
  if fn.isConstOf ``Rat.mk' && args.size ≥ 2 then
    let some num ← extractIntExpr args[0]! | return none
    let some den := (← whnf args[1]!).rawNatLit? | return none
    if den == 0 then return none
    return some (mkRat num den)
  -- Rat.mul a b
  if fn.isConstOf ``Rat.mul && args.size ≥ 2 then
    let some a ← extractRatQ args[0]! | return none
    let some b ← extractRatQ args[1]! | return none
    return some (a * b)
  -- Rat.inv a
  if fn.isConstOf ``Rat.inv && args.size ≥ 1 then
    let some a ← extractRatQ args[0]! | return none
    if a ≠ 0 then return some (1 / a)
    return some 0
  -- Rat.add a b
  if fn.isConstOf ``Rat.add && args.size ≥ 2 then
    let some a ← extractRatQ args[0]! | return none
    let some b ← extractRatQ args[1]! | return none
    return some (a + b)
  -- Rat.sub a b
  if fn.isConstOf ``Rat.sub && args.size ≥ 2 then
    let some a ← extractRatQ args[0]! | return none
    let some b ← extractRatQ args[1]! | return none
    return some (a - b)
  -- Rat.neg a
  if fn.isConstOf ``Rat.neg && args.size ≥ 1 then
    let some a ← extractRatQ args[0]! | return none
    return some (-a)
  -- Rat.div a b
  if fn.isConstOf ``Rat.div && args.size ≥ 2 then
    let some a ← extractRatQ args[0]! | return none
    let some b ← extractRatQ args[1]! | return none
    if b ≠ 0 then return some (a / b)
    return some 0
  -- Rat.ofScientific m s e (m × 10^(±e))
  if fn.isConstOf ``Rat.ofScientific && args.size ≥ 3 then
    let some m := (← whnf args[0]!).rawNatLit? | return none
    let sW ← whnf args[1]!
    let some exp := (← whnf args[2]!).rawNatLit? | return none
    let isNeg := sW.isConstOf ``Bool.true
    if isNeg then
      return some (mkRat (Int.ofNat m) (10 ^ exp))
    else
      return some ((m : ℚ) * (10 ^ exp : ℚ))
  -- OfNat.ofNat / Natural literal
  if let some n := getOfNat? e' then return some (n : ℚ)
  if let some n := e'.rawNatLit? then return some (n : ℚ)
  -- Rat.num / Rat.den projections (from whnf of constructor)
  let numExpr ← whnf (mkProj ``Rat 0 e')
  let denExpr ← whnf (mkProj ``Rat 1 e')
  let some den := denExpr.rawNatLit? | return none
  if den == 0 then return none
  let some num ← extractIntExpr numExpr | return none
  return some (mkRat num den)

/-- Extract ℚ from a Real.ofCauchy expression by evaluating the Cauchy sequence
    at index 0 and reading the resulting ℚ literal.

    Returns `(ℚ value, original ℚ Expr)`. The ℚ value is used for bounds; the
    original Expr is used in `RExpr.ratCast` so that `denote` produces an expression
    definitionally equal to the goal. This is critical because `Rat.mul`/`Rat.inv`
    are `@[extern]` and opaque to the kernel — using `mkRatExpr` would produce a
    normalized form (e.g., `19/20`) that the kernel can't equate with the original
    (`Rat.mul 95 (Rat.inv 100)`).

    CauSeq ℚ abs is a Subtype { val : ℕ → ℚ // IsCauSeq abs val }, so we project
.val (field 0 of Subtype), apply to 0, and whnf-reduce to get a concrete Rat
    constructor (Rat.mk num den proof₁ proof₂). Then project.num and.den to
    extract the ℚ value.

    This handles fractions (2/3, 1/3, etc.) that findEmbeddedNat cannot,
    since findEmbeddedNat only scans for the first raw nat literal. -/
def extractRatFromCauchy (e : Expr) : MetaM (Option (ℚ × Expr)) := do
  let args := e.getAppArgs
  if args.isEmpty then return none
  let mut seq := args.back!
  -- The CauSeq.Completion.Cauchy type is a Quotient, so seq may be
  -- Quot.mk rel causeq_val. Unwrap to get the CauSeq (Subtype) value.
  let seqW ← whnf seq
  let seqFn := seqW.getAppFn
  if seqFn.isConstOf ``Quot.mk || seqFn.isConstOf ``Quotient.mk then
    seq := seqW.getAppArgs.back!
  -- Project Subtype.val (field 0), apply to 0, and reduce
  let fAtZero ← whnf (mkApp (mkProj ``Subtype 0 seq) (mkRawNatLit 0))
  -- Try direct Rat.num/Rat.den projection first (fast path)
  let numExpr ← whnf (mkProj ``Rat 0 fAtZero)
  let denExpr ← whnf (mkProj ``Rat 1 fAtZero)
  if let some den := denExpr.rawNatLit? then
    if den ≠ 0 then
      if let some num ← extractIntExpr numExpr then
        let q := mkRat num den
        -- Use mkRatExpr for the expression (it's definitionally equal
        -- since Rat.num/den projected successfully)
        let qE ← mkRatExpr q
        return some (q, qE)
  -- Fallback: fAtZero may be an opaque Rat operation (Rat.mul, Rat.inv, etc.)
  -- that doesn't reduce under whnf. Use recursive ℚ extractor for the VALUE,
  -- then use mkRatExpr for a canonical form (avoids leaking noncomputable refs).
  if let some q ← extractRatQ fAtZero then
    let qE ← mkRatExpr q
    return some (q, qE)
  return none

-- ============================================================================
-- Recursive Reifier
-- ============================================================================

def maxDepth : ℕ := 200

/-- Memoization cache for reifyToRExpr, keyed on Expr structural hash.
    Stores `(rexprExpr, bounds)`. -/
abbrev ReifyCache := IO.Ref (Std.HashMap UInt64 (Expr × MetaBounds))
/-- Store result in cache and return it. -/
private def cacheReturn (cache : ReifyCache) (key : UInt64)
    (result : Expr × MetaBounds) : MetaM (Expr × MetaBounds) := do
  cache.modify fun m => m.insert key result
  return result

/-- Module-scope filter result cache for `Finset.filter` evaluations.
    For predicates of the form `fun x => f(x) = c` (constant-RHS equality),
    caches which elements pass the filter, keyed by `(hash f, hash reduced_c)`.
    This deduplicates filter evaluations for qudProject equivalence classes:
    worlds with `project(w₁, q) = project(w₂, q)` share the same filter result,
    avoiding redundant `reduce` calls (20 per filter × ~300 duplicate filters). -/
initialize persistentFilterCache : IO.Ref (Std.HashMap UInt64 (Array Expr)) ←
  IO.mkRef ∅

/-- Proof-free RExpr reifier for rsa_predict.
    Produces `(rexprExpr, bounds)`. The kernel verifies `denote(rexprExpr) ≡ e`
    by iota-reducing `denote`, eliminating the need for congruence proof trees.

    **Transparent steps** (unfoldDefinition?, whnf, headBeta, let-substitution) produce
    definitionally equal forms — the reified RExpr from the recursive call works
    unchanged because `denote(rexpr) ≡ e' ≡ e`.

    **Structural steps** (pattern-matching on HAdd, Real.exp, ite, etc.) build
    RExpr nodes whose `denote` is definitionally equal to the original expression.

    Uses a hash-keyed cache to avoid redundant reification of shared subexpressions. -/
partial def reifyToRExpr (cache : ReifyCache) (e : Expr) (depth : ℕ) :
    MetaM (Expr × MetaBounds) := do
  -- Increase maxRecDepth for whnf calls inside the reifier.
  -- Complex meaning functions (e.g., Innocent Exclusion exhaustification) can
  -- require deep kernel reduction during Finset.sum unfolding.
  withTheReader Core.Context (fun ctx =>
    { ctx with maxRecDepth := max ctx.maxRecDepth 8192 }) do
  if depth == 0 then
    throwError "rsa_predict: max reification depth on: {← ppExpr e}"

  -- Let binding: substitute (transparent — definitional equality)
  if e.isLet then
    return ← reifyToRExpr cache (e.letBody!.instantiate1 e.letValue!) (depth - 1)

  -- Cache lookup
  let key := hash e
  if let some result := (← cache.get).get? key then
    return result

  -- Natural literal (leaf — kernel verifies e ≡ denote(nat n))
  if let some n := getOfNat? e then
    let rexpr := mkApp (mkConst ``RExpr.nat) (mkRawNatLit n)
    return ← cacheReturn cache key (rexpr, ⟨n, n⟩)

  let fn := e.getAppFn
  let args := e.getAppArgs

  -- Cauchy-form ℝ literal: Real.ofCauchy wraps a constant Cauchy sequence
  -- from a ℚ→ℝ cast. Use RExpr.ratCast so denote produces Rat.cast,
  -- matching the goal expression. (RExpr.nat would produce Nat.cast which
  -- is not definitionally equal to Rat.cast for the kernel.)
  if fn.isConstOf ``Real.ofCauchy then
    if let some (q, qE) ← extractRatFromCauchy e then
      let rexpr := mkApp (mkConst ``RExpr.ratCast) qE
      return ← cacheReturn cache key (rexpr, ⟨q, q⟩)
    -- Fallback: scan for embedded nat (handles cases where Cauchy structure is unusual)
    if let some n := findEmbeddedNat e then
      let rexpr := mkApp (mkConst ``RExpr.nat) (mkRawNatLit n)
      return ← cacheReturn cache key (rexpr, ⟨n, n⟩)

  -- Addition: @HAdd.hAdd ℝ ℝ ℝ _ a b
  if isAppOfMin e ``HAdd.hAdd 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr := mkApp2 (mkConst ``RExpr.add) ra rb
    return ← cacheReturn cache key (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)

  if isAppOfMin e ``Add.add 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr := mkApp2 (mkConst ``RExpr.add) ra rb
    return ← cacheReturn cache key (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)

  -- Multiplication
  if isAppOfMin e ``HMul.hMul 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr := mkApp2 (mkConst ``RExpr.mul) ra rb
    return ← cacheReturn cache key (rexpr, metaEvalMul ba bb)

  if isAppOfMin e ``Mul.mul 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr := mkApp2 (mkConst ``RExpr.mul) ra rb
    return ← cacheReturn cache key (rexpr, metaEvalMul ba bb)

  -- Division
  if isAppOfMin e ``HDiv.hDiv 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr := mkApp2 (mkConst ``RExpr.div) ra rb
    let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                  else ⟨-1, 1⟩
    return ← cacheReturn cache key (rexpr, bounds)

  if isAppOfMin e ``Div.div 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr := mkApp2 (mkConst ``RExpr.div) ra rb
    let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                  else ⟨-1, 1⟩
    return ← cacheReturn cache key (rexpr, bounds)

  -- Negation
  if isAppOfMin e ``Neg.neg 3 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let rexpr := mkApp (mkConst ``RExpr.neg) ra
    return ← cacheReturn cache key (rexpr, ⟨-ba.hi, -ba.lo⟩)

  -- Subtraction
  if isAppOfMin e ``HSub.hSub 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr := mkApp2 (mkConst ``RExpr.sub) ra rb
    return ← cacheReturn cache key (rexpr, ⟨ba.lo - bb.hi, ba.hi - bb.lo⟩)

  if isAppOfMin e ``Sub.sub 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr := mkApp2 (mkConst ``RExpr.sub) ra rb
    return ← cacheReturn cache key (rexpr, ⟨ba.lo - bb.hi, ba.hi - bb.lo⟩)

  -- Real.rpow (fixed ℕ exponent)
  if fn.isConstOf ``Real.rpow && args.size ≥ 2 then
    if let some n ← resolveNat? args[1]! then
      let (rb, bb) ← reifyToRExpr cache args[0]! (depth - 1)
      let rexpr := mkApp2 (mkConst ``RExpr.rpow) rb (mkRawNatLit n)
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
      if αExprOpt.isSome || cExprOpt.isSome then
        let (αRExpr, αBounds) ← match αExprOpt with
          | some e => reifyToRExpr cache e (depth - 1)
          | none => do
            let r := mkApp (mkConst ``RExpr.nat) (mkRawNatLit 1)
            pure (r, (⟨1, 1⟩ : MetaBounds))
        if αBounds.lo == αBounds.hi && αBounds.lo > 0 && αBounds.lo.den == 1 then
          let α := αBounds.lo
          let n := α.num.toNat
          let (xRExpr, xBounds) ← reifyToRExpr cache xExpr (depth - 1)
          if xBounds.lo ≥ 0 then
            let (cRExpr, cBounds) ← match cExprOpt with
              | some e => reifyToRExpr cache e (depth - 1)
              | none => do
                let r := mkApp (mkConst ``RExpr.nat) (mkRawNatLit 0)
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
            if αExprOpt.isSome && cExprOpt.isSome then
              let rexpr := mkApp3 (mkConst ``RExpr.expMulLogSub) αRExpr xRExpr cRExpr
              return ← cacheReturn cache key (rexpr, bounds)
            -- Otherwise preserve original structure
            let logR := mkApp (mkConst ``RExpr.rlog) xRExpr
            let withSub := match cExprOpt with
              | some _ => mkApp2 (mkConst ``RExpr.sub) logR cRExpr
              | none => logR
            let withMul := match αExprOpt with
              | some _ => mkApp2 (mkConst ``RExpr.mul) αRExpr withSub
              | none => withSub
            let rexpr := mkApp (mkConst ``RExpr.rexp) withMul
            return ← cacheReturn cache key (rexpr, bounds)
    -- Fallback: reify argument normally
    let (ra, ba) ← reifyToRExpr cache args[0]! (depth - 1)
    let rexpr := mkApp (mkConst ``RExpr.rexp) ra
    let elo := (Linglib.Interval.expPoint ba.lo).lo
    let ehi := (Linglib.Interval.expPoint ba.hi).hi
    return ← cacheReturn cache key (rexpr, ⟨elo, ehi⟩)

  -- Real.log
  if fn.isConstOf ``Real.log && args.size ≥ 1 then
    let (ra, ba) ← reifyToRExpr cache args[0]! (depth - 1)
    let rexpr := mkApp (mkConst ``RExpr.rlog) ra
    let bounds := if ba.lo > 0 then
                    ⟨(evalLogPoint ba.lo).1, (evalLogPoint ba.hi).2⟩
                  else ⟨-1000, 1000⟩
    return ← cacheReturn cache key (rexpr, bounds)

  -- If-then-else (iteZero for x=0 conditions)
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
        let (rt, bt) ← reifyToRExpr cache thenBr (depth - 1)
        let (re, be) ← reifyToRExpr cache elseBr (depth - 1)
        let rexpr := mkApp3 (mkConst ``RExpr.iteZero) rc rt re
        let bounds := if bc.lo > 0 then be
                      else if bc.lo == 0 && bc.hi == 0 then bt
                      else ⟨min bt.lo be.lo, max bt.hi be.hi⟩
        return ← cacheReturn cache key (rexpr, bounds)
      -- Bool condition: ite ((expr) = true) or ite ((expr) = false)
      -- Try native evaluation first (fast, bypasses maxRecDepth), then whnf fallback
      if cArgs[0]!.isConstOf ``Bool then
        let rhsVal ← whnf cArgs[2]!
        let rhsIsTrue := rhsVal.isConstOf ``Bool.true
        let rhsIsFalse := rhsVal.isConstOf ``Bool.false
        -- Try native Bool evaluation (handles complex meaning functions like IE)
        if let some boolResult ← tryEvalBool cArgs[1]! then
          let lhsMatchesRhs := (boolResult && rhsIsTrue) || (!boolResult && rhsIsFalse)
          if lhsMatchesRhs then
            return ← reifyToRExpr cache thenBr (depth - 1)
          else
            return ← reifyToRExpr cache elseBr (depth - 1)
        -- Fallback: whnf (for expressions that can't be natively evaluated)
        let boolVal ← whnf cArgs[1]!
        let lhsIsTrue := boolVal.isConstOf ``Bool.true
        let lhsIsFalse := boolVal.isConstOf ``Bool.false
        if (lhsIsTrue && rhsIsTrue) || (lhsIsFalse && rhsIsFalse) then
          return ← reifyToRExpr cache thenBr (depth - 1)
        else if (lhsIsTrue && rhsIsFalse) || (lhsIsFalse && rhsIsTrue) then
          return ← reifyToRExpr cache elseBr (depth - 1)
    -- Transparent: whnf fallback
    let e' ← whnf e
    if !e.equal e' then
      return ← reifyToRExpr cache e' (depth - 1)
    throwError "rsa_predict: unsupported ite condition: {← ppExpr cond}"

  -- Decidable.rec (from whnf'd ite) — iteZero
  -- Decidable.rec is definitionally equal to ite, so iteZero denote matches.
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
        let dummyTrueProof := mkApp2 (mkConst ``sorryAx [levelZero]) prop (toExpr true)
        let thenBody := (Expr.app isTrueBr dummyTrueProof).headBeta
        let negProp ← mkAppM ``Not #[prop]
        let dummyFalseProof := mkApp2 (mkConst ``sorryAx [levelZero]) negProp (toExpr true)
        let elseBody := (Expr.app isFalseBr dummyFalseProof).headBeta
        let (rt, bt) ← reifyToRExpr cache thenBody (depth - 1)
        let (re, be) ← reifyToRExpr cache elseBody (depth - 1)
        let rexpr := mkApp3 (mkConst ``RExpr.iteZero) rc rt re
        let bounds := if bc.lo > 0 then be
                      else if bc.lo == 0 && bc.hi == 0 then bt
                      else ⟨min bt.lo be.lo, max bt.hi be.hi⟩
        return ← cacheReturn cache key (rexpr, bounds)

  -- Structural sum unfolding: Finset.sum Finset.univ f  and
  -- Finset.sum (Finset.filter p Finset.univ) f
  -- Enumerate elements via getFiniteElems and apply f to each, avoiding whnf
  -- on the summands (which would eagerly evaluate complex meaning functions).
  -- The filter variant evaluates the predicate at meta-time via the DecidablePred
  -- instance, including only elements where the predicate holds. This avoids the
  -- expensive Multiset/Quotient whnf fallback that Finset.filter would otherwise
  -- trigger (e.g., qudProject in KaoEtAl2014 Hyperbole: 15s → <1s).
  let fnName := fn.constName?
  if fnName == some ``Finset.sum && args.size ≥ 6 then
    let fBody := args[5]!
    let finsetExpr := args[4]!
    let finsetFn := finsetExpr.getAppFn
    -- Case 1: Finset.sum Finset.univ f — sum over all elements
    if finsetFn.isConstOf ``Finset.univ then
      let T := args[0]!
      if let some (_, elems) ← try? (getFiniteElems T) then
        if elems.size > 0 then
          let firstApp := Expr.app fBody elems[0]!
          let firstResult ← reifyToRExpr cache firstApp.headBeta (depth - 1)
          let mut accRExpr := firstResult.1
          let mut accBounds := firstResult.2
          for i in List.range (elems.size - 1) do
            let elemApp := Expr.app fBody elems[i + 1]!
            let (ri, bi) ← reifyToRExpr cache elemApp.headBeta (depth - 1)
            let rexpr := mkApp2 (mkConst ``RExpr.add) accRExpr ri
            let bounds : MetaBounds := ⟨accBounds.lo + bi.lo, accBounds.hi + bi.hi⟩
            accRExpr := rexpr
            accBounds := bounds
          return ← cacheReturn cache key (accRExpr, accBounds)
    -- Case 2: Finset.sum (Finset.filter p decInst Finset.univ) f
    -- Evaluate filter predicate at meta-time, sum only matching elements.
    if finsetFn.isConstOf ``Finset.filter then
      let filterArgs := finsetExpr.getAppArgs
      -- Finset.filter : {α} → (p : α → Prop) → [DecidablePred p] → Finset α → Finset α
      -- filterArgs: [α, p, decidablePredInst, innerFinset]
      if filterArgs.size ≥ 4 then
        let innerFinset := filterArgs[3]!
        if innerFinset.getAppFn.isConstOf ``Finset.univ then
          let T := args[0]!
          if let some (_, elems) ← try? (getFiniteElems T) then
            if elems.size > 0 then
              let predExpr := filterArgs[1]!
              let decPredInst := filterArgs[2]!
              -- Filter-result caching: for predicates fun x => f(x) = c where
              -- c is constant (no bound variable), cache the filtered elements
              -- by (hash f, hash reduced_c). This deduplicates filter evaluations
              -- for qudProject: worlds in the same equivalence class produce the
              -- same filter result but have different predicate expressions.
              let mut filterCacheKey? : Option UInt64 := none
              if predExpr.isLambda then
                let predBody := predExpr.bindingBody!
                if predBody.isAppOfArity ``Eq 3 then
                  let eqArgs := predBody.getAppArgs
                  let rhs := eqArgs[2]!
                  if !rhs.hasLooseBVars then
                    let rhsReduced ← whnf rhs
                    filterCacheKey? :=
                      some (hash (eqArgs[1]!) * 6364136223846793005 + hash rhsReduced)
              -- Check filter cache
              let mut filteredElems : Array Expr := #[]
              let mut filterEvaluated := false
              if let some fck := filterCacheKey? then
                if let some cached := (← persistentFilterCache.get).get? fck then
                  filteredElems := cached
                  filterEvaluated := true
              -- Evaluate filter at meta-time if not cached
              if !filterEvaluated then
                let mut filterOk := true
                for elem in elems do
                  let decApp := Expr.app decPredInst elem
                  -- Use whnf (faster than reduce for simple Decidable evaluations)
                  let reduced ← whnf decApp
                  let reducedFn := reduced.getAppFn
                  if reducedFn.isConstOf ``isTrue || reducedFn.isConstOf ``Decidable.isTrue then
                    filteredElems := filteredElems.push elem
                  else if reducedFn.isConstOf ``isFalse || reducedFn.isConstOf ``Decidable.isFalse then
                    pure ()  -- skip
                  else
                    -- whnf didn't resolve — try full reduce
                    let fullReduced ← reduce decApp
                    let fullFn := fullReduced.getAppFn
                    if fullFn.isConstOf ``isTrue || fullFn.isConstOf ``Decidable.isTrue then
                      filteredElems := filteredElems.push elem
                    else
                      -- Predicate couldn't be evaluated; fall through to whnf path
                      filteredElems := #[]  -- signal failure
                      filterOk := false
                      break
                -- Cache filter result on success
                if filterOk then
                  if let some fck := filterCacheKey? then
                    persistentFilterCache.modify fun m => m.insert fck filteredElems
              if filteredElems.size > 0 then
                -- Equivalence-class dedup: cache by (fBody, filtered elements).
                -- Different filter predicates selecting the same elements with the
                -- same summand function produce the same result. Deduplicates e.g.
                -- qudProject calls for worlds in the same QUD equivalence class.
                let filterKey := filteredElems.foldl
                  (fun (h : UInt64) elem => h * 31 + hash elem) (hash fBody)
                if let some result := (← cache.get).get? filterKey then
                  return ← cacheReturn cache key result
                let firstApp := Expr.app fBody filteredElems[0]!
                let firstResult ← reifyToRExpr cache firstApp.headBeta (depth - 1)
                let mut accRExpr := firstResult.1
                let mut accBounds := firstResult.2
                for i in List.range (filteredElems.size - 1) do
                  let elemApp := Expr.app fBody filteredElems[i + 1]!
                  let (ri, bi) ← reifyToRExpr cache elemApp.headBeta (depth - 1)
                  let rexpr := mkApp2 (mkConst ``RExpr.add) accRExpr ri
                  let bounds : MetaBounds := ⟨accBounds.lo + bi.lo, accBounds.hi + bi.hi⟩
                  accRExpr := rexpr
                  accBounds := bounds
                cache.modify fun m => m.insert filterKey (accRExpr, accBounds)
                return ← cacheReturn cache key (accRExpr, accBounds)
              else if filteredElems.size == 0 then
                -- Empty filter result — sum is 0
                -- If from cache, we know it's genuinely empty.
                -- Otherwise check if genuinely empty vs break-out failure.
                let genuinelyEmpty ← if filterEvaluated then pure true
                  else elems.allM fun elem => do
                    let decApp := Expr.app decPredInst elem
                    let reduced ← whnf decApp
                    let reducedFn := reduced.getAppFn
                    if reducedFn.isConstOf ``isFalse || reducedFn.isConstOf ``Decidable.isFalse then
                      return true
                    let fullReduced ← reduce decApp
                    let fullFn := fullReduced.getAppFn
                    return fullFn.isConstOf ``isFalse || fullFn.isConstOf ``Decidable.isFalse
                if genuinelyEmpty then
                  -- Genuinely empty: sum is 0
                  let zeroExpr := mkApp (mkConst ``RExpr.nat) (mkRawNatLit 0)
                  return ← cacheReturn cache key (zeroExpr, ⟨0, 0⟩)

  -- Fallback for other summation forms (transparent — whnf)
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

  -- Default: unfold one definition, headBeta (transparent)
  if let some e' ← unfoldDefinition? e then
    return ← reifyToRExpr cache e'.headBeta (depth - 1)

  -- Reducible whnf (transparent)
  let eR ← withReducible do whnf e
  if !e.equal eR then
    return ← reifyToRExpr cache eR (depth - 1)

  -- Full whnf fallback (transparent)
  let e' ← whnf e
  if !e.equal e' then
    return ← reifyToRExpr cache e' (depth - 1)

  -- Tertiary: detect numeric literals via isDefEq (leaf)
  let eType ← inferType e
  if eType.isConstOf ``Real then
    -- Fast path: check Cauchy form before the isDefEq loop
    if e.getAppFn.isConstOf ``Real.ofCauchy then
      if let some (q, qE) ← extractRatFromCauchy e then
        let rexpr := mkApp (mkConst ``RExpr.ratCast) qE
        return ← cacheReturn cache key (rexpr, ⟨q, q⟩)
      if let some n := findEmbeddedNat e then
        let rexpr := mkApp (mkConst ``RExpr.nat) (mkRawNatLit n)
        return ← cacheReturn cache key (rexpr, ⟨n, n⟩)
    for n in ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ) do
      let nE := mkRawNatLit n
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, nE, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e target catch _ => return false
      if isEq then
        let rexpr := mkApp (mkConst ``RExpr.nat) nE
        return ← cacheReturn cache key (rexpr, ⟨n, n⟩)

  -- Quaternary: detect binary ops via isDefEq
  if args.size ≥ 2 then
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    let isAdd ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HAdd.hAdd #[a, b]) catch _ => return false
    if isAdd then
      let (ra, ba) ← reifyToRExpr cache a (depth - 1)
      let (rb, bb) ← reifyToRExpr cache b (depth - 1)
      let rexpr := mkApp2 (mkConst ``RExpr.add) ra rb
      return ← cacheReturn cache key (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)
    let isMul ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HMul.hMul #[a, b]) catch _ => return false
    if isMul then
      let (ra, ba) ← reifyToRExpr cache a (depth - 1)
      let (rb, bb) ← reifyToRExpr cache b (depth - 1)
      let rexpr := mkApp2 (mkConst ``RExpr.mul) ra rb
      return ← cacheReturn cache key (rexpr, metaEvalMul ba bb)
    let isDiv ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HDiv.hDiv #[a, b]) catch _ => return false
    if isDiv then
      let (ra, ba) ← reifyToRExpr cache a (depth - 1)
      let (rb, bb) ← reifyToRExpr cache b (depth - 1)
      let rexpr := mkApp2 (mkConst ``RExpr.div) ra rb
      let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                    else ⟨-1, 1⟩
      return ← cacheReturn cache key (rexpr, bounds)

  -- Detect exp/log/inv/rpow via isDefEq
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
      let rexpr := mkApp (mkConst ``RExpr.rexp) ra
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
      let rexpr := mkApp (mkConst ``RExpr.rlog) ra
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
      let rexpr := mkApp (mkConst ``RExpr.inv) ra
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
        let rexpr := mkApp2 (mkConst ``RExpr.rpow) rb (mkRawNatLit n)
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
    if let some (q, _) ← extractRatFromCauchy e' then return q
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
      if let some (q, _) ← extractRatFromCauchy e' then return q
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
  withTheReader Core.Context (fun ctx =>
    { ctx with maxRecDepth := max ctx.maxRecDepth 8192 }) do
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
