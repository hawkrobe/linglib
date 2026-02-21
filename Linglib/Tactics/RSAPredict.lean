import Lean
import Linglib.Theories.Pragmatics.RSA.Core.Verified
import Linglib.Core.Interval.ReflectInterval

set_option autoImplicit false

/-!
# RSAPredict — Level-Aware Verified RSA Predictions

The `rsa_predict` tactic proves ℝ comparison goals on RSA models by:

1. Pattern-matching the goal to identify the comparison form (L1, L1_latent, sums)
2. Reifying each S1 score individually via RExpr → ℚ interval arithmetic
3. Computing L1/L1_latent/marginal bounds entirely at meta level
4. Applying a bridge axiom from `RSA.Verified` with the computed ℚ separation

## Supported Goal Forms

- `cfg.L1 u w₁ > cfg.L1 u w₂` — L1 world comparison
- `cfg.L1_latent u l₁ > cfg.L1_latent u l₂` — latent variable inference
- `Σ cfg.L1 u wᵢ > Σ cfg.L1 u wⱼ` — marginal comparison (same utterance)
- `Σ cfg.L1 u₁ wᵢ > Σ cfg.L1 u₂ wⱼ` — cross-utterance sum comparison

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

-- ============================================================================
-- Meta-level QInterval Combinators
-- ============================================================================

/-- Round a nonneg ℚ down to `bits` binary digits: floor(q · 2^bits) / 2^bits.
    The result has a power-of-2 denominator, preventing denominator blowup. -/
private def roundDownBin (q : ℚ) (bits : ℕ) : ℚ :=
  let scale := (2 ^ bits : ℕ)
  let n := q.num.toNat * scale / q.den  -- Nat division = floor for nonneg
  (n : ℚ) / (scale : ℚ)

/-- Round a nonneg ℚ up to `bits` binary digits: ceil(q · 2^bits) / 2^bits. -/
private def roundUpBin (q : ℚ) (bits : ℕ) : ℚ :=
  let scale := (2 ^ bits : ℕ)
  let n := (q.num.toNat * scale + q.den - 1) / q.den  -- ceil
  (n : ℚ) / (scale : ℚ)

/-- Round MetaBounds outward (lo down, hi up) to `bits` binary digits.
    Maintains soundness: the rounded interval contains the original.
    Assumes both bounds are nonneg (always true for RSA scores). -/
private def roundBounds (b : MetaBounds) (bits : ℕ := 48) : MetaBounds :=
  if b.lo == b.hi then b  -- point interval: already exact, rounding would only widen
  else ⟨roundDownBin b.lo bits, roundUpBin b.hi bits⟩

private def metaQIAdd (a b : MetaBounds) : MetaBounds := ⟨a.lo + b.lo, a.hi + b.hi⟩

private def metaQISumMap (scores : Array MetaBounds) : MetaBounds :=
  scores.foldl metaQIAdd ⟨0, 0⟩

private def metaQIDivPosSafe (num denom : MetaBounds) : MetaBounds :=
  if denom.hi ≤ 0 then ⟨0, 0⟩  -- all scores = 0 ⟹ policy = 0 (RationalAction convention)
  else if num.lo ≥ 0 && denom.lo > 0 then ⟨num.lo / denom.hi, num.hi / denom.lo⟩
  else ⟨0, 1⟩

private def metaQINormalize (scores : Array MetaBounds) (targetIdx : ℕ) : MetaBounds :=
  let target := scores[targetIdx]!
  if target.hi ≤ 0 then ⟨0, 0⟩  -- target score is zero → policy = 0
  else
    -- If all non-target scores are zero, policy is exactly 1 (no interval widening)
    let othersNonZero := (List.range scores.size).any fun i =>
      i != targetIdx && scores[i]!.hi > 0
    if !othersNonZero then ⟨1, 1⟩
    else roundBounds (metaQIDivPosSafe target (metaQISumMap scores))

/-- Compute L1 unnormalized score at meta level using MetaBounds.
      L1(u,w) = worldPrior(w) · Σ_l latentPrior(w,l) · S1_policy(l,w,u)
    where S1_policy(l,w,u) = S1(l,w,u) / Σ_{u'} S1(l,w,u').
    lpValues is indexed as lpValues[wIdx * nL + lIdx]. -/
private def metaL1Score
    (nL nW nU : ℕ)
    (s1Bounds : Array MetaBounds)
    (wpValues : Array ℚ) (lpValues : Array ℚ)
    (uIdx wIdx : ℕ) : MetaBounds :=
  let wp : MetaBounds := ⟨wpValues[wIdx]!, wpValues[wIdx]!⟩
  let latentSum := (List.range nL).foldl (init := (⟨0, 0⟩ : MetaBounds)) fun acc il =>
    let lp : MetaBounds := ⟨lpValues[wIdx * nL + il]!, lpValues[wIdx * nL + il]!⟩
    let s1Scores := Array.range nU |>.map fun iu =>
      s1Bounds[il * nW * nU + wIdx * nU + iu]!
    let s1Policy := metaQINormalize s1Scores uIdx
    metaQIAdd acc (roundBounds (metaEvalMul' lp s1Policy))
  roundBounds (metaEvalMul' wp latentSum)

/-- Find the index of `target` in `elems` by definitional equality. -/
private def findElemIdx (elems : Array Expr) (target : Expr) : MetaM ℕ := do
  for i in List.range elems.size do
    if elems[i]!.equal target then return i
  for i in List.range elems.size do
    if ← isDefEq elems[i]! target then return i
  throwError "rsa_predict: cannot find element in enum list"

-- ============================================================================

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

/-- Extract a ℤ from an expression in constructor form (Int.ofNat n or Int.negSucc n). -/
private def extractIntExpr (e : Expr) : MetaM (Option ℤ) := do
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
private def extractRatFromCauchy (e : Expr) : MetaM (Option ℚ) := do
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

private def maxDepth : ℕ := 200

/-- Memoization cache for reifyToRExpr, keyed on Expr structural hash. -/
private abbrev ReifyCache := IO.Ref (Std.HashMap UInt64 (Expr × MetaBounds))
/-- Store result in cache and return it. -/
private def cacheReturn (cache : ReifyCache) (key : UInt64) (result : Expr × MetaBounds) :
    MetaM (Expr × MetaBounds) := do
  cache.modify fun m => m.insert key result
  return result

/-- Simplified RExpr reifier for rsa_predict.
    Produces RExpr values + meta-level bounds.
    Uses a hash-keyed cache to avoid redundant reification of shared subexpressions. -/
private partial def reifyToRExpr (cache : ReifyCache) (e : Expr) (depth : ℕ) :
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
  if let some n := getOfNat?' e then
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
  if isAppOfMin' e ``HAdd.hAdd 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.add #[ra, rb]
    return ← cacheReturn cache key (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)

  if isAppOfMin' e ``Add.add 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.add #[ra, rb]
    return ← cacheReturn cache key (rexpr, ⟨ba.lo + bb.lo, ba.hi + bb.hi⟩)

  -- Multiplication
  if isAppOfMin' e ``HMul.hMul 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.mul #[ra, rb]
    return ← cacheReturn cache key (rexpr, metaEvalMul' ba bb)

  if isAppOfMin' e ``Mul.mul 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.mul #[ra, rb]
    return ← cacheReturn cache key (rexpr, metaEvalMul' ba bb)

  -- Division
  if isAppOfMin' e ``HDiv.hDiv 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.div #[ra, rb]
    let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                  else ⟨-1, 1⟩
    return ← cacheReturn cache key (rexpr, bounds)

  if isAppOfMin' e ``Div.div 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.div #[ra, rb]
    let bounds := if ba.lo ≥ 0 && bb.lo > 0 then ⟨ba.lo / bb.hi, ba.hi / bb.lo⟩
                  else ⟨-1, 1⟩
    return ← cacheReturn cache key (rexpr, bounds)

  -- Negation
  if isAppOfMin' e ``Neg.neg 3 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.neg #[ra]
    return ← cacheReturn cache key (rexpr, ⟨-ba.hi, -ba.lo⟩)

  -- Subtraction
  if isAppOfMin' e ``HSub.hSub 6 then
    let (ra, ba) ← reifyToRExpr cache args[4]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[5]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.sub #[ra, rb]
    return ← cacheReturn cache key (rexpr, ⟨ba.lo - bb.hi, ba.hi - bb.lo⟩)

  if isAppOfMin' e ``Sub.sub 4 then
    let (ra, ba) ← reifyToRExpr cache args[2]! (depth - 1)
    let (rb, bb) ← reifyToRExpr cache args[3]! (depth - 1)
    let rexpr ← mkAppM ``RExpr.sub #[ra, rb]
    return ← cacheReturn cache key (rexpr, ⟨ba.lo - bb.hi, ba.hi - bb.lo⟩)

  -- Real.rpow
  if fn.isConstOf ``Real.rpow && args.size ≥ 2 then
    if let some n ← resolveNat?' args[1]! then
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
      if isAppOfMin' inner ``HMul.hMul 6 then
        (some (inner.getAppArgs[4]!), inner.getAppArgs[5]!)
      else if isAppOfMin' inner ``Mul.mul 4 then
        (some (inner.getAppArgs[2]!), inner.getAppArgs[3]!)
      else (none, inner)
    -- Try to decompose: rest = log(x) - c, or just log(x) with c=0
    let (logCandidate, cExprOpt) :=
      if isAppOfMin' rest ``HSub.hSub 6 then
        (rest.getAppArgs[4]!, some (rest.getAppArgs[5]!))
      else if isAppOfMin' rest ``Sub.sub 4 then
        (rest.getAppArgs[2]!, some (rest.getAppArgs[3]!))
      else (rest, none)
    -- Check if logCandidate is Real.log(x)
    if logCandidate.getAppFn.isConstOf ``Real.log && logCandidate.getAppNumArgs ≥ 1 then
      let xExpr := logCandidate.getAppArgs[0]!
      -- Reify sub-parts (none of these trigger logPoint)
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
          let bounds := metaEvalMul' xPowBounds expFactorBounds
          -- Build RExpr preserving original structure
          let logR ← mkAppM ``RExpr.rlog #[xRExpr]
          let subR ← mkAppM ``RExpr.sub #[logR, cRExpr]
          let mulR ← mkAppM ``RExpr.mul #[αRExpr, subR]
          let rexpr ← mkAppM ``RExpr.rexp #[mulR]
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
                    ⟨(evalLogPoint' ba.lo).1, (evalLogPoint' ba.hi).2⟩
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
      if let some 0 := getOfNat?' rhsC then
        let lhsC := cArgs[1]!
        let (rc, bc) ← reifyToRExpr cache lhsC (depth - 1)
        if bc.lo > 0 then
          let (re, be) ← reifyToRExpr cache elseBr (depth - 1)
          let rexpr ← mkAppM ``RExpr.iteZero #[rc, ← mkAppM ``RExpr.nat #[mkRawNatLit 0], re]
          return ← cacheReturn cache key (rexpr, be)
        else if bc.lo == 0 && bc.hi == 0 then
          let (rt, bt) ← reifyToRExpr cache thenBr (depth - 1)
          let rexpr ← mkAppM ``RExpr.iteZero #[rc, rt, ← mkAppM ``RExpr.nat #[mkRawNatLit 0]]
          return ← cacheReturn cache key (rexpr, bt)
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
      if let some 0 := getOfNat?' rhsC then
        let (rc, bc) ← reifyToRExpr cache lhsC (depth - 1)
        if bc.lo > 0 then
          let negProp ← mkAppM ``Not #[prop]
          let dummyProof := mkApp2 (mkConst ``sorryAx [levelZero]) negProp (toExpr true)
          let elseBody := (Expr.app isFalseBr dummyProof).headBeta
          let (re, be) ← reifyToRExpr cache elseBody (depth - 1)
          let rexpr ← mkAppM ``RExpr.iteZero #[rc, ← mkAppM ``RExpr.nat #[mkRawNatLit 0], re]
          return ← cacheReturn cache key (rexpr, be)
        else if bc.lo == 0 && bc.hi == 0 then
          let dummyProof := mkApp2 (mkConst ``sorryAx [levelZero]) prop (toExpr true)
          let thenBody := (Expr.app isTrueBr dummyProof).headBeta
          let (rt, bt) ← reifyToRExpr cache thenBody (depth - 1)
          let rexpr ← mkAppM ``RExpr.iteZero #[rc, rt, ← mkAppM ``RExpr.nat #[mkRawNatLit 0]]
          return ← cacheReturn cache key (rexpr, bt)

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
      return ← cacheReturn cache key (rexpr, metaEvalMul' ba bb)
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
                      ⟨(evalLogPoint' ba.lo).1, (evalLogPoint' ba.hi).2⟩
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
      if let some n ← resolveNat?' exp then
        let (rb, bb) ← reifyToRExpr cache base (depth - 1)
        let rexpr ← mkAppM ``RExpr.rpow #[rb, mkRawNatLit n]
        let bounds := if n == 0 then ⟨1, 1⟩
                      else if bb.lo ≥ 0 then ⟨bb.lo ^ n, bb.hi ^ n⟩
                      else ⟨0, 1⟩
        return ← cacheReturn cache key (rexpr, bounds)

  throwError "rsa_predict: cannot reify: {← ppExpr e} (depth: {depth})"

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
  -- Inv (a⁻¹ = 1/a)
  if isAppOfMin' e ``Inv.inv 3 then
    let a ← extractRat e.getAppArgs[2]!
    if a ≠ 0 then return some (1 / a)
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

/-- Extract RSA config and arguments from a policy expression.
    Returns (cfg, l, w, u) where the expression is `cfg.S1 l w u`. -/
private def parseS1Policy (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  -- Try to unfold to cfg.S1agent(l).policy w u
  if let some (ra, w, u) := ← unfoldToPolicy e then
    -- Check if ra is cfg.S1agent l
    let mut raC := ra
    for _ in List.range 5 do
      let fn := raC.getAppFn
      let args := raC.getAppArgs
      if fn.isConstOf ``RSA.RSAConfig.S1agent && args.size ≥ 6 then
        let cfg := args[4]!
        let l := args[5]!
        return some (cfg, l, w, u)
      if let some ra' ← unfoldDefinition? raC then
        raC := ra'.headBeta
      else break
  return none

-- ============================================================================
-- Main Tactic
-- ============================================================================

-- ============================================================================
-- Goal Form Parsing
-- ============================================================================

/-- Parsed goal forms that rsa_predict can handle. -/
private inductive GoalForm where
  /-- cfg.L1 u w₁ > cfg.L1 u w₂ -/
  | l1Compare (cfg u w₁ w₂ : Expr)
  /-- (ws₁.map (cfg.L1 u)).sum > (ws₂.map (cfg.L1 u)).sum (marginal) -/
  | l1Marginal (cfg u : Expr) (ws₁ ws₂ : Array Expr)
  /-- cfg.L1_latent u l₁ > cfg.L1_latent u l₂ -/
  | l1Latent (cfg u l₁ l₂ : Expr)
  /-- (ws₁.map (cfg.L1 u₁)).sum > (ws₂.map (cfg.L1 u₂)).sum (cross-utterance) -/
  | l1CrossUtterance (cfg u₁ : Expr) (ws₁ : Array Expr) (u₂ : Expr) (ws₂ : Array Expr)
  /-- cfg.S1 l w u₁ > cfg.S1 l w u₂ -/
  | s1Compare (cfg l w u₁ u₂ : Expr)

/-- Try to unfold an expression to `cfg.L1_latent u l`. -/
private def parseL1Latent (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut current := e
  for _ in List.range 10 do
    let fn := current.getAppFn
    let args := current.getAppArgs
    if fn.isConstOf ``RSA.RSAConfig.L1_latent && args.size ≥ 5 then
      return some (args[4]!, args[5]!, args[6]!)  -- cfg, u, l
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none

/-- Collect L1 policy summands from an expression.
    Returns (cfg, u, ws) where ws are the world arguments, or none.
    Handles Finset.sum, List.sum of map, and nested HAdd of L1 terms. -/
private partial def collectL1Summands (e : Expr) : MetaM (Option (Expr × Expr × Array Expr)) := do
  -- Try single L1 term first
  if let some (cfg, u, w) ← parseL1Policy e then
    return some (cfg, u, #[w])
  -- Try HAdd of L1 terms
  if isAppOfMin' e ``HAdd.hAdd 6 then
    let a := e.getAppArgs[4]!
    let b := e.getAppArgs[5]!
    if let some (cfg1, u1, ws1) ← collectL1Summands a then
      if let some (cfg2, u2, ws2) ← collectL1Summands b then
        if (← isDefEq cfg1 cfg2) && (← isDefEq u1 u2) then
          return some (cfg1, u1, ws1 ++ ws2)
        -- Different utterances: return cfg1, u1, ws1 for LHS; caller handles
  -- Try Finset.sum: unfold and recurse
  let fn := e.getAppFn
  if fn.constName? == some ``Finset.sum ||
     fn.constName? == some ``Multiset.sum ||
     fn.constName? == some ``Multiset.fold ||
     fn.constName? == some ``List.foldr ||
     fn.constName? == some ``List.foldl ||
     fn.constName? == some ``List.sum ||
     fn.constName? == some ``Quot.lift then
    let e' ← whnf e
    if !e.equal e' then
      return ← collectL1Summands e'
  -- Try unfolding
  if let some e' ← unfoldDefinition? e then
    return ← collectL1Summands e'.headBeta
  return none

/-- Collect L1 summands allowing different utterances on each side.
    Returns (cfg, u, ws) pairs. For cross-utterance goals, the two sides
    may have different u values. -/
private partial def collectL1SummandsAnyU (e : Expr) :
    MetaM (Option (Expr × Array (Expr × Array Expr))) := do
  -- Try single L1 term first
  if let some (cfg, u, w) ← parseL1Policy e then
    return some (cfg, #[(u, #[w])])
  -- Try HAdd of L1 terms (may have different utterances)
  if isAppOfMin' e ``HAdd.hAdd 6 then
    let a := e.getAppArgs[4]!
    let b := e.getAppArgs[5]!
    if let some (cfg1, groups1) ← collectL1SummandsAnyU a then
      if let some (cfg2, groups2) ← collectL1SummandsAnyU b then
        if ← isDefEq cfg1 cfg2 then
          -- Merge groups by utterance
          let mut merged := groups1
          for (u2, ws2) in groups2 do
            let mut found := false
            for i in List.range merged.size do
              if ← isDefEq merged[i]!.1 u2 then
                merged := merged.set! i (merged[i]!.1, merged[i]!.2 ++ ws2)
                found := true
                break
            unless found do
              merged := merged.push (u2, ws2)
          return some (cfg1, merged)
  -- Try Finset.sum: unfold and recurse
  let fn := e.getAppFn
  if fn.constName? == some ``Finset.sum ||
     fn.constName? == some ``Multiset.sum ||
     fn.constName? == some ``Multiset.fold ||
     fn.constName? == some ``List.foldr ||
     fn.constName? == some ``List.foldl ||
     fn.constName? == some ``List.sum ||
     fn.constName? == some ``Quot.lift then
    let e' ← whnf e
    if !e.equal e' then
      return ← collectL1SummandsAnyU e'
  -- Try unfolding
  if let some e' ← unfoldDefinition? e then
    return ← collectL1SummandsAnyU e'.headBeta
  return none

/-- Parse the goal into a GoalForm. -/
private def parseGoalForm (lhs rhs : Expr) : MetaM GoalForm := do
  -- Path A: Both sides are cfg.L1 u w
  if let some (cfg, u, w₁) ← parseL1Policy lhs then
    if let some (cfg₂, _u₂, w₂) ← parseL1Policy rhs then
      if ← isDefEq cfg cfg₂ then
        return .l1Compare cfg u w₁ w₂

  -- Path B: cfg.L1_latent u l₁ > cfg.L1_latent u l₂
  if let some (cfg, u, l₁) ← parseL1Latent lhs then
    if let some (cfg₂, _u₂, l₂) ← parseL1Latent rhs then
      if ← isDefEq cfg cfg₂ then
        return .l1Latent cfg u l₁ l₂

  -- Path B2: cfg.S1 l w u₁ > cfg.S1 l w u₂
  if let some (cfg, l, w, u₁) ← parseS1Policy lhs then
    if let some (cfg₂, _l₂, _w₂, u₂) ← parseS1Policy rhs then
      if ← isDefEq cfg cfg₂ then
        return .s1Compare cfg l w u₁ u₂

  -- Path C/D: sums of L1 terms
  if let some (cfg1, groups1) ← collectL1SummandsAnyU lhs then
    if let some (cfg2, groups2) ← collectL1SummandsAnyU rhs then
      if ← isDefEq cfg1 cfg2 then
        -- Same utterance on both sides → marginal
        if groups1.size == 1 && groups2.size == 1 then
          let (u1, ws1) := groups1[0]!
          let (u2, ws2) := groups2[0]!
          if ← isDefEq u1 u2 then
            return .l1Marginal cfg1 u1 ws1 ws2
          else
            return .l1CrossUtterance cfg1 u1 ws1 u2 ws2
        -- Different utterances → cross-utterance
        -- Flatten all groups into one side each
        let allWs1 := groups1.foldl (init := #[]) fun acc (_, ws) => acc ++ ws
        let allWs2 := groups2.foldl (init := #[]) fun acc (_, ws) => acc ++ ws
        -- For cross-utterance, we need exactly one u per side
        if groups1.size == 1 && groups2.size == 1 then
          return .l1CrossUtterance cfg1 groups1[0]!.1 allWs1 groups2[0]!.1 allWs2

  throwError "rsa_predict: cannot parse goal. Expected one of:\n\
    • cfg.L1 u w₁ > cfg.L1 u w₂\n\
    • cfg.L1_latent u l₁ > cfg.L1_latent u l₂\n\
    • cfg.S1 l w u₁ > cfg.S1 l w u₂\n\
    • Σ ... cfg.L1 u ... > Σ ... cfg.L1 u ...\n\
    • (cfg.L1 u₁ w₁ + ...) > (cfg.L1 u₂ w₃ + ...)"

-- ============================================================================
-- Shared S1 Reification
-- ============================================================================

/-- Shared infrastructure: extract config info, reify all S1 scores.
    Returns (U, W, L types, element arrays, s1Bounds, wpValues, lpValues). -/
private def reifyS1Scores (cfg : Expr) :
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

-- ============================================================================
-- Meta-level L1 Latent Score
-- ============================================================================

/-- Compute latent inference score at meta level:
    latent_score(l) = Σ_w worldPrior(w) · latentPrior(w,l) · S1_policy(l,w,u)
    where S1_policy(l,w,u) = S1(l,w,u) / Σ_{u'} S1(l,w,u').
    lpValues is indexed as lpValues[wIdx * nL + lIdx]. -/
private def metaL1LatentScore
    (nL nW nU : ℕ)
    (s1Bounds : Array MetaBounds)
    (wpValues : Array ℚ) (lpValues : Array ℚ)
    (uIdx lIdx : ℕ) : MetaBounds :=
  let worldSum := (List.range nW).foldl (init := (⟨0, 0⟩ : MetaBounds)) fun acc iw =>
    let wp : MetaBounds := ⟨wpValues[iw]!, wpValues[iw]!⟩
    let lp : MetaBounds := ⟨lpValues[iw * nL + lIdx]!, lpValues[iw * nL + lIdx]!⟩
    let s1Scores := Array.range nU |>.map fun iu =>
      s1Bounds[lIdx * nW * nU + iw * nU + iu]!
    let s1Policy := metaQINormalize s1Scores uIdx
    metaQIAdd acc (roundBounds (metaEvalMul' (metaEvalMul' wp lp) s1Policy))
  roundBounds worldSum

/-- Compute L1 policy bounds at meta level (score / total).
    Used for cross-utterance comparisons where denominators differ. -/
private def metaL1Policy
    (nL nW nU : ℕ)
    (s1Bounds : Array MetaBounds)
    (wpValues : Array ℚ) (lpValues : Array ℚ)
    (uIdx : ℕ) (allWIndices : Array ℕ) (targetWIdx : ℕ) : MetaBounds :=
  let scores := allWIndices.map fun wIdx =>
    metaL1Score nL nW nU s1Bounds wpValues lpValues uIdx wIdx
  let totalBounds := metaQISumMap scores
  let targetScore := metaL1Score nL nW nU s1Bounds wpValues lpValues uIdx targetWIdx
  roundBounds (metaQIDivPosSafe targetScore totalBounds)

-- ============================================================================
-- Proof Construction Helpers
-- ============================================================================

/-- Prove `hi₂ < lo₁` via native_decide and return the proof term. -/
private def proveQSeparation (hi₂ lo₁ : ℚ) : TacticM Expr := do
  let hi2Expr ← mkRatExpr hi₂
  let lo1Expr ← mkRatExpr lo₁
  let sepType ← mkAppM ``LT.lt #[hi2Expr, lo1Expr]
  let sepMVar ← mkFreshExprMVar sepType
  let savedGoals ← getGoals
  setGoals [sepMVar.mvarId!]
  try
    evalTactic (← `(tactic| native_decide))
  catch e =>
    setGoals savedGoals
    throwError "rsa_predict: native_decide failed on ℚ comparison: {e.toMessageData}"
  setGoals savedGoals
  return sepMVar

private def proveQLeq (hi₁ lo₂ : ℚ) : TacticM Expr := do
  let hi1Expr ← mkRatExpr hi₁
  let lo2Expr ← mkRatExpr lo₂
  let leType ← mkAppM ``LE.le #[hi1Expr, lo2Expr]
  let leMVar ← mkFreshExprMVar leType
  let savedGoals ← getGoals
  setGoals [leMVar.mvarId!]
  try
    evalTactic (← `(tactic| native_decide))
  catch e =>
    setGoals savedGoals
    throwError "rsa_predict: native_decide failed on ℚ comparison: {e.toMessageData}"
  setGoals savedGoals
  return leMVar

/-- Assign proof to goal, with cast/simp fallbacks. -/
private def assignWithCastFallback (goal : MVarId) (proof : Expr) : TacticM Unit := do
  let proofType ← inferType proof
  let goalType ← goal.getType
  if ← isDefEq proofType goalType then
    goal.assign proof
  else
    let goalWithH ← goal.assert `h_rsa proofType proof
    let (_, finalGoal) ← goalWithH.intro1
    setGoals [finalGoal]
    -- Try various simplification strategies to bridge the gap
    -- between List.map/sum form and direct addition form
    try
      evalTactic (← `(tactic| simp only [List.map, List.sum_cons, List.sum_nil, add_zero] at *))
      evalTactic (← `(tactic| linarith))
    catch _ =>
    try evalTactic (← `(tactic| assumption_mod_cast))
    catch _ =>
      try evalTactic (← `(tactic| push_cast at *; assumption))
      catch _ => evalTactic (← `(tactic| norm_cast at *; assumption))

-- ============================================================================
-- Main Tactic
-- ============================================================================

/-- `rsa_predict` proves RSA prediction goals by level-aware interval arithmetic.

    Supported goal forms:
    - `cfg.L1 u w₁ > cfg.L1 u w₂` — L1 world comparison
    - `¬(cfg.L1 u w₁ > cfg.L1 u w₂)` — L1 non-strict (implicature canceled)
    - `cfg.L1_latent u l₁ > cfg.L1_latent u l₂` — latent inference
    - `cfg.S1 l w u₁ > cfg.S1 l w u₂` — S1 speaker comparison
    - `¬(cfg.S1 l w u₁ > cfg.S1 l w u₂)` — S1 non-strict
    - `Σ s, cfg.L1 u (s, a₁) > Σ s, cfg.L1 u (s, a₂)` — marginal comparison
    - `cfg.L1 u₁ w₁ + ... > cfg.L1 u₂ w₃ + ...` — cross-utterance sum -/
elab "rsa_predict" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Try native_decide first (handles ℚ, Bool, finite types)
  try
    evalTactic (← `(tactic| native_decide))
    return
  catch _ => pure ()

  -- ¬(_ > _): detect as P → False (Not is @[reducible], so whnf reduces @Not P)
  let goalTypeWhnf ← whnf goalType
  if let .forallE _ inner (.const ``False []) _ := goalTypeWhnf then do
    let innerFn := inner.getAppFn
    let innerArgs := inner.getAppArgs
    unless innerFn.isConstOf ``GT.gt && innerArgs.size ≥ 4 do
      throwError "rsa_predict: expected goal of the form `¬(_ > _)`, got: {← ppExpr goalType}"
    let lhs := innerArgs[2]!
    let rhs := innerArgs[3]!
    let goalForm ← parseGoalForm lhs rhs
    match goalForm with
    | .l1Compare cfg u w₁ w₂ => do
      logInfo m!"rsa_predict: parsed goal as ¬(L1 comparison)"
      let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
        reifyS1Scores cfg
      let uIdx ← findElemIdx allUElems u
      let w1Idx ← findElemIdx allWElems w₁
      let w2Idx ← findElemIdx allWElems w₂
      let l1_w1 := metaL1Score allLElems.size allWElems.size allUElems.size
        s1Bounds wpValues lpValues uIdx w1Idx
      let l1_w2 := metaL1Score allLElems.size allWElems.size allUElems.size
        s1Bounds wpValues lpValues uIdx w2Idx
      logInfo m!"rsa_predict: L1(u, w₁) ∈ [{l1_w1.lo}, {l1_w1.hi}]"
      logInfo m!"rsa_predict: L1(u, w₂) ∈ [{l1_w2.lo}, {l1_w2.hi}]"
      unless l1_w1.hi ≤ l1_w2.lo do
        throwError "rsa_predict: cannot prove ¬(L1 w₁ > L1 w₂): w₁.hi = {l1_w1.hi} > w₂.lo = {l1_w2.lo}"
      let leProof ← proveQLeq l1_w1.hi l1_w2.lo
      let hi1Expr ← mkRatExpr l1_w1.hi
      let lo2Expr ← mkRatExpr l1_w2.lo
      let proof ← mkAppM ``RSA.Verified.L1_not_gt_of_precomputed
        #[cfg, u, w₁, w₂, hi1Expr, lo2Expr, leProof]
      assignWithCastFallback goal proof
      logInfo m!"rsa_predict: ✓ proved via L1_not_gt_of_precomputed"
      return
    | .s1Compare cfg l w u₁ u₂ => do
      logInfo m!"rsa_predict: parsed goal as ¬(S1 comparison)"
      let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, _, _) ←
        reifyS1Scores cfg
      let lIdx ← findElemIdx allLElems l
      let wIdx ← findElemIdx allWElems w
      let u1Idx ← findElemIdx allUElems u₁
      let u2Idx ← findElemIdx allUElems u₂
      let nU := allUElems.size
      let nW := allWElems.size
      let idx1 := lIdx * nW * nU + wIdx * nU + u1Idx
      let idx2 := lIdx * nW * nU + wIdx * nU + u2Idx
      let s1_u1 := s1Bounds[idx1]!
      let s1_u2 := s1Bounds[idx2]!
      logInfo m!"rsa_predict: S1_score(u₁) ∈ [{s1_u1.lo}, {s1_u1.hi}]"
      logInfo m!"rsa_predict: S1_score(u₂) ∈ [{s1_u2.lo}, {s1_u2.hi}]"
      unless s1_u1.hi ≤ s1_u2.lo do
        throwError "rsa_predict: cannot prove ¬(S1 u₁ > S1 u₂): u₁.hi = {s1_u1.hi} > u₂.lo = {s1_u2.lo}"
      let leProof ← proveQLeq s1_u1.hi s1_u2.lo
      let hi1Expr ← mkRatExpr s1_u1.hi
      let lo2Expr ← mkRatExpr s1_u2.lo
      let proof ← mkAppM ``RSA.Verified.S1_not_gt_of_precomputed
        #[cfg, l, w, u₁, u₂, hi1Expr, lo2Expr, leProof]
      assignWithCastFallback goal proof
      logInfo m!"rsa_predict: ✓ proved via S1_not_gt_of_precomputed"
      return
    | _ => throwError "rsa_predict: ¬(_ > _) only supported for L1 and S1 comparisons, got: {← ppExpr goalType}"

  let fn := goalType.getAppFn
  let args := goalType.getAppArgs

  -- GT.gt: lhs > rhs
  unless fn.isConstOf ``GT.gt && args.size ≥ 4 do
    throwError "rsa_predict: expected goal of the form `_ > _` or `¬(_ > _)`, got: {← ppExpr goalType}"

  let lhs := args[2]!
  let rhs := args[3]!

  let goalForm ← parseGoalForm lhs rhs

  match goalForm with
  | .l1Compare cfg u w₁ w₂ => do
    logInfo m!"rsa_predict: parsed goal as L1 comparison"
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
      reifyS1Scores cfg

    let uIdx ← findElemIdx allUElems u
    let w1Idx ← findElemIdx allWElems w₁
    let w2Idx ← findElemIdx allWElems w₂

    let l1_w1 := metaL1Score allLElems.size allWElems.size allUElems.size
      s1Bounds wpValues lpValues uIdx w1Idx
    let l1_w2 := metaL1Score allLElems.size allWElems.size allUElems.size
      s1Bounds wpValues lpValues uIdx w2Idx

    logInfo m!"rsa_predict: L1(u, w₁) ∈ [{l1_w1.lo}, {l1_w1.hi}]"
    logInfo m!"rsa_predict: L1(u, w₂) ∈ [{l1_w2.lo}, {l1_w2.hi}]"

    unless l1_w2.hi < l1_w1.lo do
      throwError "rsa_predict: L1 scores not separated: w₂.hi = {l1_w2.hi} ≥ w₁.lo = {l1_w1.lo}"

    let sepProof ← proveQSeparation l1_w2.hi l1_w1.lo
    let hi2Expr ← mkRatExpr l1_w2.hi
    let lo1Expr ← mkRatExpr l1_w1.lo
    let proof ← mkAppM ``RSA.Verified.L1_gt_of_precomputed
      #[cfg, u, w₁, w₂, hi2Expr, lo1Expr, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via L1_gt_of_precomputed"

  | .l1Marginal cfg u ws₁ ws₂ => do
    logInfo m!"rsa_predict: parsed goal as marginal L1 comparison ({ws₁.size} vs {ws₂.size} worlds)"
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
      reifyS1Scores cfg

    let uIdx ← findElemIdx allUElems u

    -- Sum L1 scores over each world set
    let mut marg1 : MetaBounds := ⟨0, 0⟩
    for w in ws₁ do
      let wIdx ← findElemIdx allWElems w
      let score := metaL1Score allLElems.size allWElems.size allUElems.size
        s1Bounds wpValues lpValues uIdx wIdx
      marg1 := metaQIAdd marg1 score
    marg1 := roundBounds marg1

    let mut marg2 : MetaBounds := ⟨0, 0⟩
    for w in ws₂ do
      let wIdx ← findElemIdx allWElems w
      let score := metaL1Score allLElems.size allWElems.size allUElems.size
        s1Bounds wpValues lpValues uIdx wIdx
      marg2 := metaQIAdd marg2 score
    marg2 := roundBounds marg2

    logInfo m!"rsa_predict: marginal₁ ∈ [{marg1.lo}, {marg1.hi}]"
    logInfo m!"rsa_predict: marginal₂ ∈ [{marg2.lo}, {marg2.hi}]"

    unless marg2.hi < marg1.lo do
      throwError "rsa_predict: marginal scores not separated: hi₂ = {marg2.hi} ≥ lo₁ = {marg1.lo}"

    let sepProof ← proveQSeparation marg2.hi marg1.lo
    let hi2Expr ← mkRatExpr marg2.hi
    let lo1Expr ← mkRatExpr marg1.lo
    -- Build world lists as Lean exprs
    let W ← inferType ws₁[0]!
    let ws1ListExpr ← mkListLit W ws₁.toList
    let ws2ListExpr ← mkListLit W ws₂.toList
    let proof ← mkAppM ``RSA.Verified.L1_sum_gt_of_precomputed
      #[cfg, u, ws1ListExpr, u, ws2ListExpr, hi2Expr, lo1Expr, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via L1_sum_gt_of_precomputed (marginal)"

  | .l1Latent cfg u l₁ l₂ => do
    logInfo m!"rsa_predict: parsed goal as L1_latent comparison"
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
      reifyS1Scores cfg

    let uIdx ← findElemIdx allUElems u
    let l1Idx ← findElemIdx allLElems l₁
    let l2Idx ← findElemIdx allLElems l₂

    let score1 := metaL1LatentScore allLElems.size allWElems.size allUElems.size
      s1Bounds wpValues lpValues uIdx l1Idx
    let score2 := metaL1LatentScore allLElems.size allWElems.size allUElems.size
      s1Bounds wpValues lpValues uIdx l2Idx

    logInfo m!"rsa_predict: latent_score(l₁) ∈ [{score1.lo}, {score1.hi}]"
    logInfo m!"rsa_predict: latent_score(l₂) ∈ [{score2.lo}, {score2.hi}]"

    unless score2.hi < score1.lo do
      throwError "rsa_predict: latent scores not separated: hi₂ = {score2.hi} ≥ lo₁ = {score1.lo}"

    let sepProof ← proveQSeparation score2.hi score1.lo
    let hi2Expr ← mkRatExpr score2.hi
    let lo1Expr ← mkRatExpr score1.lo
    let proof ← mkAppM ``RSA.Verified.L1_latent_gt_of_precomputed
      #[cfg, u, l₁, l₂, hi2Expr, lo1Expr, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via L1_latent_gt_of_precomputed"

  | .l1CrossUtterance cfg u₁ ws₁ u₂ ws₂ => do
    logInfo m!"rsa_predict: parsed goal as cross-utterance L1 sum ({ws₁.size} vs {ws₂.size})"
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
      reifyS1Scores cfg

    let nL := allLElems.size
    let nW := allWElems.size
    let nU := allUElems.size

    -- Compute policy bounds for each utterance
    let allWIndices := Array.range nW

    let u1Idx ← findElemIdx allUElems u₁
    let mut psum1 : MetaBounds := ⟨0, 0⟩
    for w in ws₁ do
      let wIdx ← findElemIdx allWElems w
      let policy := metaL1Policy nL nW nU s1Bounds wpValues lpValues u1Idx allWIndices wIdx
      psum1 := metaQIAdd psum1 policy
    psum1 := roundBounds psum1

    let u2Idx ← findElemIdx allUElems u₂
    let mut psum2 : MetaBounds := ⟨0, 0⟩
    for w in ws₂ do
      let wIdx ← findElemIdx allWElems w
      let policy := metaL1Policy nL nW nU s1Bounds wpValues lpValues u2Idx allWIndices wIdx
      psum2 := metaQIAdd psum2 policy
    psum2 := roundBounds psum2

    logInfo m!"rsa_predict: policy_sum₁ ∈ [{psum1.lo}, {psum1.hi}]"
    logInfo m!"rsa_predict: policy_sum₂ ∈ [{psum2.lo}, {psum2.hi}]"

    unless psum2.hi < psum1.lo do
      throwError "rsa_predict: policy sums not separated: hi₂ = {psum2.hi} ≥ lo₁ = {psum1.lo}"

    let sepProof ← proveQSeparation psum2.hi psum1.lo
    let hi2Expr ← mkRatExpr psum2.hi
    let lo1Expr ← mkRatExpr psum1.lo
    let W ← inferType ws₁[0]!
    let ws1ListExpr ← mkListLit W ws₁.toList
    let ws2ListExpr ← mkListLit W ws₂.toList
    let proof ← mkAppM ``RSA.Verified.L1_sum_gt_of_precomputed
      #[cfg, u₁, ws1ListExpr, u₂, ws2ListExpr, hi2Expr, lo1Expr, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via L1_sum_gt_of_precomputed"

  | .s1Compare cfg l w u₁ u₂ => do
    logInfo m!"rsa_predict: parsed goal as S1 comparison"
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, _, _) ←
      reifyS1Scores cfg

    let lIdx ← findElemIdx allLElems l
    let wIdx ← findElemIdx allWElems w
    let u1Idx ← findElemIdx allUElems u₁
    let u2Idx ← findElemIdx allUElems u₂

    let nU := allUElems.size
    let nW := allWElems.size
    let idx1 := lIdx * nW * nU + wIdx * nU + u1Idx
    let idx2 := lIdx * nW * nU + wIdx * nU + u2Idx
    let s1_u1 := s1Bounds[idx1]!
    let s1_u2 := s1Bounds[idx2]!

    logInfo m!"rsa_predict: S1_score(u₁) ∈ [{s1_u1.lo}, {s1_u1.hi}]"
    logInfo m!"rsa_predict: S1_score(u₂) ∈ [{s1_u2.lo}, {s1_u2.hi}]"

    unless s1_u2.hi < s1_u1.lo do
      throwError "rsa_predict: S1 scores not separated: hi₂ = {s1_u2.hi} ≥ lo₁ = {s1_u1.lo}"

    let sepProof ← proveQSeparation s1_u2.hi s1_u1.lo
    let hi2Expr ← mkRatExpr s1_u2.hi
    let lo1Expr ← mkRatExpr s1_u1.lo
    let proof ← mkAppM ``RSA.Verified.S1_gt_of_precomputed
      #[cfg, l, w, u₁, u₂, hi2Expr, lo1Expr, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via S1_gt_of_precomputed"

end Linglib.Tactics
