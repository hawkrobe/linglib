import Lean
import Linglib.Core.Interval.ReflectInterval

set_option autoImplicit false

/-!
# RSAPredict Helpers

Low-level expression utilities, `MetaBounds` interval arithmetic, and enum extraction
used across the RSAPredict tactic submodules.
-/

namespace Tactics.RSAPredict

open Lean Meta Elab Tactic
open Interval

-- ============================================================================
-- Expr Inspection Helpers
-- ============================================================================

/-- Extract a natural number from `@OfNat.ofNat T n inst`. -/
def getOfNat? (e : Expr) : Option ℕ := do
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  e.appFn!.appArg!.rawNatLit?

/-- Extract a natural number from `@Nat.cast T inst n`. -/
def getNatCast? (e : Expr) : Option ℕ := do
  guard (e.isAppOfArity ``Nat.cast 3)
  e.getAppArgs[2]!.rawNatLit?

def getNat? (e : Expr) : Option ℕ :=
  e.rawNatLit? <|> getOfNat? e <|> getNatCast? e

def isAppOfMin (e : Expr) (name : Name) (minArgs : ℕ) : Bool :=
  e.getAppFn.isConstOf name && e.getAppNumArgs ≥ minArgs

/-- Try to extract a natural number, unfolding/reducing as needed. -/
def resolveNat? (e : Expr) : MetaM (Option ℕ) := do
  if let some n := getNat? e then return some n
  let e' ← whnf e
  if let some n := getNat? e' then return some n
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
-- Meta-level Interval Arithmetic
-- ============================================================================

/-- Meta-level interval bounds for early checks. -/
structure MetaBounds where
  lo : ℚ
  hi : ℚ
  deriving Inhabited

def metaEvalMul (a b : MetaBounds) : MetaBounds :=
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
def roundDownBin (q : ℚ) (bits : ℕ) : ℚ :=
  let scale := (2 ^ bits : ℕ)
  let n := q.num.toNat * scale / q.den  -- Nat division = floor for nonneg
  (n : ℚ) / (scale : ℚ)

/-- Round a nonneg ℚ up to `bits` binary digits: ceil(q · 2^bits) / 2^bits. -/
def roundUpBin (q : ℚ) (bits : ℕ) : ℚ :=
  let scale := (2 ^ bits : ℕ)
  let n := (q.num.toNat * scale + q.den - 1) / q.den  -- ceil
  (n : ℚ) / (scale : ℚ)

/-- Round MetaBounds outward (lo down, hi up) to `bits` binary digits.
    Maintains soundness: the rounded interval contains the original.
    Assumes both bounds are nonneg (always true for RSA scores). -/
def roundBounds (b : MetaBounds) (bits : ℕ := 48) : MetaBounds :=
  if b.lo == b.hi then b  -- point interval: already exact, rounding would only widen
  else ⟨roundDownBin b.lo bits, roundUpBin b.hi bits⟩

def metaQIAdd (a b : MetaBounds) : MetaBounds := ⟨a.lo + b.lo, a.hi + b.hi⟩

def metaQISumMap (scores : Array MetaBounds) : MetaBounds :=
  scores.foldl metaQIAdd ⟨0, 0⟩

def metaQIDivPosSafe (num denom : MetaBounds) : MetaBounds :=
  if denom.hi ≤ 0 then ⟨0, 0⟩  -- all scores = 0 ⟹ policy = 0 (RationalAction convention)
  else if num.lo ≥ 0 && denom.lo > 0 then ⟨num.lo / denom.hi, num.hi / denom.lo⟩
  else ⟨0, 1⟩

def metaQINormalize (scores : Array MetaBounds) (targetIdx : ℕ) : MetaBounds :=
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
def metaL1Score
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
    metaQIAdd acc (roundBounds (metaEvalMul lp s1Policy))
  roundBounds (metaEvalMul wp latentSum)

/-- Compute latent inference score at meta level:
    latent_score(l) = Σ_w worldPrior(w) · latentPrior(w,l) · S1_policy(l,w,u)
    where S1_policy(l,w,u) = S1(l,w,u) / Σ_{u'} S1(l,w,u').
    lpValues is indexed as lpValues[wIdx * nL + lIdx]. -/
def metaL1LatentScore
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
    metaQIAdd acc (roundBounds (metaEvalMul (metaEvalMul wp lp) s1Policy))
  roundBounds worldSum

/-- Compute L1 policy bounds at meta level (score / total).
    Used for cross-utterance comparisons where denominators differ. -/
def metaL1Policy
    (nL nW nU : ℕ)
    (s1Bounds : Array MetaBounds)
    (wpValues : Array ℚ) (lpValues : Array ℚ)
    (uIdx : ℕ) (allWIndices : Array ℕ) (targetWIdx : ℕ) : MetaBounds :=
  let scores := allWIndices.map fun wIdx =>
    metaL1Score nL nW nU s1Bounds wpValues lpValues uIdx wIdx
  let totalBounds := metaQISumMap scores
  let targetScore := metaL1Score nL nW nU s1Bounds wpValues lpValues uIdx targetWIdx
  roundBounds (metaQIDivPosSafe targetScore totalBounds)

/-- Compute S2 policy bounds at meta level (cross-world comparison).
    S2(u|w) = L1(u,w) / Σ_{u'} L1(u',w), where L1 is the **normalized** posterior.
    S2agent.score(w,u) = cfg.L1(u,w) = L1agent.policy(u,w). -/
def metaS2Score
    (nL nW nU : ℕ)
    (s1Bounds : Array MetaBounds)
    (wpValues : Array ℚ) (lpValues : Array ℚ)
    (allUIndices : Array ℕ) (targetUIdx wIdx : ℕ) : MetaBounds :=
  let allWIndices := Array.range nW
  let scores := allUIndices.map fun uIdx =>
    metaL1Policy nL nW nU s1Bounds wpValues lpValues uIdx allWIndices wIdx
  let totalBounds := metaQISumMap scores
  let targetScore := metaL1Policy nL nW nU s1Bounds wpValues lpValues targetUIdx allWIndices wIdx
  roundBounds (metaQIDivPosSafe targetScore totalBounds)

-- ============================================================================
-- Utility Functions
-- ============================================================================

/-- Find the index of `target` in `elems` by definitional equality. -/
def findElemIdx (elems : Array Expr) (target : Expr) : MetaM ℕ := do
  for i in List.range elems.size do
    if elems[i]!.equal target then return i
  for i in List.range elems.size do
    if ← isDefEq elems[i]! target then return i
  throwError "rsa_predict: cannot find element in enum list"

/-- Extract a concrete List from a Lean Expr, extracting cons cells. -/
def extractList (e : Expr) : MetaM (Array Expr) := do
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
partial def getFiniteElems (T : Expr) : MetaM (Expr × Array Expr) := do
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
  -- Handle Fin n: enumerate ⟨0, proof⟩, ⟨1, proof⟩, ..., ⟨n-1, proof⟩
  if T'.isAppOfArity ``Fin 1 then
    let nExpr := T'.getAppArgs[0]!
    let some n ← resolveNat? nExpr
      | throwError "rsa_predict: Fin argument is not a concrete natural number"
    if n == 0 then
      let listExpr ← mkListLit T []
      return (listExpr, #[])
    let nExprR ← whnf nExpr  -- reduce e.g. 10 + 1 → 11
    let mut elems : Array Expr := #[]
    for i in List.range n do
      let iLit := mkRawNatLit i
      let ltProp ← mkAppOptM ``LT.lt #[mkConst ``Nat, none, iLit, nExprR]
      let proof ← mkDecideProof ltProp
      let finElem := mkApp3 (mkConst ``Fin.mk []) nExprR iLit proof
      elems := elems.push finElem
    let listExpr ← mkListLit T elems.toList
    return (listExpr, elems)
  -- Try: enumerate constructors of an inductive type
  if let .const name _ := T'.getAppFn then
    if let some info := (← getEnv).find? name then
      if let .inductInfo iv := info then
        let env ← getEnv
        let tArgs := T'.getAppArgs
        let levels := if let .const _ ls := T'.getAppFn then ls else []
        -- Case 1: all nullary constructors (enum with no fields)
        let allNullary := iv.ctors.all fun c =>
          match env.find? c with
          | some (.ctorInfo ci) => ci.numParams + ci.numFields == iv.numParams
          | _ => false
        if allNullary then
          let elems := iv.ctors.toArray.map fun c =>
            mkAppN (mkConst c levels) tArgs
          let listExpr ← mkListLit T elems.toList
          return (listExpr, elems)
        -- Case 2: single constructor with exactly one field (wrapper structure).
        -- Recursively enumerate the field type and wrap in the constructor.
        -- Handles Degree, Threshold, and similar Fin-wrapping structures.
        if iv.ctors.length == 1 then
          let ctorName := iv.ctors.head!
          if let some (.ctorInfo ci) := env.find? ctorName then
            if ci.numFields == 1 then
              let ctorApplied := mkAppN (mkConst ctorName levels) tArgs
              let ctorType ← inferType ctorApplied
              -- Extract the single field's type
              let fieldType ← forallTelescopeReducing ctorType fun fvars _ => do
                if fvars.size ≥ 1 then
                  inferType fvars[0]!
                else
                  throwError "rsa_predict: expected at least one field in constructor"
              let (_, fieldElems) ← getFiniteElems fieldType
              let elems := fieldElems.map fun fe => mkApp ctorApplied fe
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

/-- Build a Lean Expr for a ℚ literal. -/
def mkRatExpr (q : ℚ) : MetaM Expr := do
  if q.den == 1 then
    -- Integer: just use Nat.cast or neg
    if q.num ≥ 0 then
      mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.num.natAbs]
    else
      let nat ← mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.num.natAbs]
      mkAppM ``Neg.neg #[nat]
  else
    -- Fraction: num / den
    let numExpr ← if q.num ≥ 0 then
      mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.num.natAbs]
    else
      let nat ← mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.num.natAbs]
      mkAppM ``Neg.neg #[nat]
    let denExpr ← mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit q.den]
    mkAppM ``HDiv.hDiv #[numExpr, denExpr]

-- ============================================================================
-- Native Bool Evaluation
-- ============================================================================

/-- Evaluate a closed `Bool` expression via native code compilation.
    Returns `some true` or `some false` on success, `none` if compilation fails
    (e.g., expression has free variables or references uncompiled defs).

    This is much faster than `whnf` for complex Bool computations (e.g.,
    Innocent Exclusion exhaustification) because it bypasses the kernel
    reducer's `maxRecDepth` limit and runs compiled code. -/
private unsafe def tryEvalBoolUnsafe (e : Expr) : MetaM (Option Bool) := do
  try
    let result ← evalExpr Bool (mkConst ``Bool) e
    return some result
  catch _ =>
    return none

@[implemented_by tryEvalBoolUnsafe]
opaque tryEvalBool (e : Expr) : MetaM (Option Bool)

end Tactics.RSAPredict
