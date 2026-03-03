import Linglib.Theories.Pragmatics.RSA.Core.ConfigData
import Linglib.Core.Interval.QInterval
import Linglib.Core.Interval.PadeExp
import Linglib.Core.Interval.RpowInterval
import Linglib.Core.Interval.LogInterval

set_option autoImplicit false

/-!
# RSAVerify — Computable L1 Pipeline for Reflection-Based Verification

Computable pipeline that mirrors the ℝ L0→S1→L1 computation in `RSAConfig`.
Used by `native_decide` to verify RSA predictions.

The pipeline tracks lower and upper bounds as separate ℚ values, avoiding
`Finset.toList` (which is noncomputable). All summation uses `Finset.sum`
over ℚ, which is computable.

For `beliefBased` and `qudBelief` patterns (α ∈ ℕ), bounds are **exact**:
lo = hi throughout. For patterns with `exp`/`log`, bounds have width from
Padé approximation.
-/

namespace RSA.Verify

open Linglib.Interval

-- ============================================================================
-- Bounds: proof-free (lo, hi) pair for computable pipeline
-- ============================================================================

/-- Lower and upper bounds for a nonneg real value. No validity proof
    (lo ≤ hi) — this is enforced by construction and verified in the
    soundness theorem. -/
structure Bounds where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

instance : Inhabited Bounds := ⟨⟨0, 0⟩⟩

def Bounds.exact (q : ℚ) : Bounds := ⟨q, q⟩
def Bounds.zero : Bounds := ⟨0, 0⟩

def Bounds.add (a b : Bounds) : Bounds := ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Interval subtraction: [a.lo - b.hi, a.hi - b.lo]. -/
def Bounds.sub (a b : Bounds) : Bounds := ⟨a.lo - b.hi, a.hi - b.lo⟩

/-- Multiply nonneg bounds by a nonneg scalar. -/
def Bounds.scaleNonneg (q : ℚ) (b : Bounds) : Bounds := ⟨q * b.lo, q * b.hi⟩

/-- Multiply two bounds (4-corner for general, nonneg shortcut when possible). -/
def Bounds.mul (a b : Bounds) : Bounds :=
  if a.lo ≥ 0 && b.lo ≥ 0 then ⟨a.lo * b.lo, a.hi * b.hi⟩
  else
    let c00 := a.lo * b.lo; let c01 := a.lo * b.hi
    let c10 := a.hi * b.lo; let c11 := a.hi * b.hi
    ⟨min (min c00 c01) (min c10 c11), max (max c00 c01) (max c10 c11)⟩

/-- Divide nonneg numerator by positive denominator. -/
def Bounds.divPos (a b : Bounds) : Bounds :=
  if b.lo > 0 && a.lo ≥ 0 then ⟨a.lo / b.hi, a.hi / b.lo⟩
  else if b.lo > 0 then ⟨a.lo / b.lo, a.hi / b.lo⟩ -- a may be negative
  else ⟨0, 0⟩ -- total = 0, policy = 0

/-- Convert Bounds to QInterval (with sorry'd validity for the proof layer). -/
noncomputable def Bounds.toQInterval (b : Bounds) : QInterval :=
  ⟨b.lo, b.hi, by sorry⟩

-- ============================================================================
-- Exp/Log via PadeExp (extract lo/hi from QInterval)
-- ============================================================================

/-- Bounds for exp(q) via Padé approximation. -/
def expBounds (q : ℚ) : Bounds :=
  let qi := expPoint q
  ⟨qi.lo, qi.hi⟩

/-- Bounds for exp over an interval [lo, hi].
    Uses monotonicity: exp(lo) ≤ exp(x) ≤ exp(hi). -/
def expIntervalBounds (b : Bounds) : Bounds :=
  let lo_qi := expPoint b.lo
  let hi_qi := expPoint b.hi
  ⟨lo_qi.lo, hi_qi.hi⟩

-- ============================================================================
-- Pow: p^α as exact ℚ or interval
-- ============================================================================

/-- Bounds for p^α where p ≥ 0. Exact when α is a natural number (α.den = 1),
    interval via exp(α·log(p)) otherwise. -/
def powBounds (p : ℚ) (α : ℚ) : Bounds :=
  if p = 0 then Bounds.zero
  else if α.den = 1 then Bounds.exact (p ^ α.num.toNat)
  else if hp : 0 < p then
    let li := logPoint p hp
    expIntervalBounds ⟨α * li.lo, α * li.hi⟩
  else Bounds.zero

-- ============================================================================
-- L0: Exact ℚ Policy
-- ============================================================================

/-- Compute L0 policy as exact ℚ: meaning(l,u,w) / Σ_w' meaning(l,u,w').
    Returns 0 if total is 0 (no world has nonzero meaning). -/
def computeL0Rat {U W L : Type*} [Fintype W]
    (meaning : L → U → W → ℚ) (l : L) (u : U) (w : W) : ℚ :=
  let total := Finset.univ.sum (meaning l u)
  if total = 0 then 0 else meaning l u w / total

-- ============================================================================
-- S1 Score Bounds (dispatch on S1ScoreSpec)
-- ============================================================================

/-- Compute S1 score bounds, dispatching on the scoring specification.

    For `beliefBased` / `qudBelief`: exact (lo = hi = L0^α).
    For `qudAction` / `beliefAction`: algebraic rewrite
      `exp(α·(log x - c)) = x^α · exp(-α·c)`, exact base + Padé discount.
    For `actionBased`: Padé `exp` directly.
    For `beliefWeighted`: full interval pipeline. -/
def computeS1ScoreBounds {U W L : Type*} [Fintype W] [DecidableEq W] [DecidableEq L]
    (spec : S1ScoreSpec U W L)
    (meaning : L → U → W → ℚ) (α : ℚ)
    (l : L) (w : W) (u : U) : Bounds :=
  match spec with
  | .beliefBased =>
    powBounds (computeL0Rat meaning l u w) α
  | .qudBelief project =>
    let l0 : W → ℚ := computeL0Rat meaning l u
    let projected := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    powBounds projected α
  | .qudAction cost project =>
    let l0 : W → ℚ := computeL0Rat meaning l u
    let projected := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    if projected = 0 then Bounds.zero
    else
      -- exp(α·(log projected - cost u)) = projected^α · exp(-α · cost u)
      (powBounds projected α).mul (expBounds (-(α * cost u)))
  | .beliefAction cost =>
    let p := computeL0Rat meaning l u w
    if p = 0 then Bounds.zero
    else (powBounds p α).mul (expBounds (-(α * cost u)))
  | .weightedBeliefAction infWeight bonus =>
    let p := computeL0Rat meaning l u w
    if p = 0 then Bounds.zero
    else
      -- exp(α · (γ · log(p) + bonus(u)))
      let logBnds : Bounds :=
        if hp : 0 < p then
          let li := logPoint p hp
          ⟨infWeight * li.lo, infWeight * li.hi⟩
        else Bounds.zero
      let argBounds : Bounds := ⟨α * (logBnds.lo + bonus u), α * (logBnds.hi + bonus u)⟩
      expIntervalBounds argBounds
  | .actionBased cost =>
    let p := computeL0Rat meaning l u w
    expBounds (α * (p - cost u))
  | .beliefWeighted belief quality =>
    if quality l u then
      let argLo := Finset.univ.sum fun s =>
        let p := computeL0Rat meaning l u s
        let bq := belief l s
        if hp : 0 < p then bq * (logPoint p hp).lo
        else bq * (-1000)
      let argHi := Finset.univ.sum fun s =>
        let p := computeL0Rat meaning l u s
        let bq := belief l s
        if hp : 0 < p then bq * (logPoint p hp).hi
        else bq * (-1000)
      let scaled : Bounds := ⟨α * argLo, α * argHi⟩
      expIntervalBounds scaled
    else Bounds.zero
  | .combinedUtility terms _ =>
    let p := computeL0Rat meaning l u w
    let hasActiveLog := terms.any fun t => match t with
      | .logInformativity weight => weight l != 0
      | _ => false
    if hasActiveLog && p == 0 then Bounds.zero
    else
      let evalTerm : RSA.S1UtilityTerm U W L → Bounds := fun t => match t with
        | .logInformativity weight =>
          if hp : 0 < p then
            (Bounds.exact (weight l)).mul ⟨(logPoint p hp).lo, (logPoint p hp).hi⟩
          else Bounds.zero
        | .expectedValue weight value =>
          let ev := Finset.univ.sum fun w' => computeL0Rat meaning l u w' * value w'
          Bounds.exact (weight l * ev)
        | .constant fn => Bounds.exact (fn l u)
      let termSum := terms.foldl (fun acc t => acc.add (evalTerm t)) Bounds.zero
      let scaled : Bounds := ⟨α * termSum.lo, α * termSum.hi⟩
      expIntervalBounds scaled

-- ============================================================================
-- S1 Policy Bounds
-- ============================================================================

/-- Compute S1 policy bounds: score(u) / Σ_{u'} score(u').
    Uses `Finset.sum` for totals (computable over ℚ). -/
def computeS1PolicyBounds {U W L : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W] [DecidableEq L]
    (spec : S1ScoreSpec U W L)
    (meaning : L → U → W → ℚ) (α : ℚ)
    (l : L) (w : W) (u : U) : Bounds :=
  let myScore := computeS1ScoreBounds spec meaning α l w u
  -- Total bounds: lo of total = Σ lo_i, hi of total = Σ hi_i
  let totalLo := Finset.univ.sum fun u' => (computeS1ScoreBounds spec meaning α l w u').lo
  let totalHi := Finset.univ.sum fun u' => (computeS1ScoreBounds spec meaning α l w u').hi
  -- Sole-utterance shortcut: if total = myScore (all others are [0,0]),
  -- policy = score/score = 1. Avoids divPos interval widening from Padé.
  if myScore.lo > 0 && totalLo == myScore.lo && totalHi == myScore.hi then
    Bounds.exact 1
  else
    Bounds.divPos myScore ⟨totalLo, totalHi⟩

-- ============================================================================
-- L1 Score Bounds
-- ============================================================================

/-- Compute L1 unnormalized score bounds:
    L1_score(u,w) = worldPrior(w) · Σ_l latentPrior(w,l) · S1_policy(l,w,u).

    Uses `Finset.sum` over latent variables (computable over ℚ). -/
def computeL1ScoreBounds {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (u : U) (w : W) : Bounds :=
  let latentSumLo := Finset.univ.sum fun (l : d.Latent) =>
    d.latentPrior w l *
      (computeS1PolicyBounds d.s1Spec d.meaning d.α l w u).lo
  let latentSumHi := Finset.univ.sum fun (l : d.Latent) =>
    d.latentPrior w l *
      (computeS1PolicyBounds d.s1Spec d.meaning d.α l w u).hi
  ⟨d.worldPrior w * latentSumLo, d.worldPrior w * latentSumHi⟩

-- ============================================================================
-- Separation Check
-- ============================================================================

/-- Check that L1 score for (u₁,w₁) is strictly greater than for (u₂,w₂).
    Uses bound separation: score₂.hi < score₁.lo. -/
def checkL1ScoreGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (u₁ : U) (w₁ : W) (u₂ : U) (w₂ : W) : Bool :=
  let b₁ := computeL1ScoreBounds d u₁ w₁
  let b₂ := computeL1ScoreBounds d u₂ w₂
  b₂.hi < b₁.lo

-- ============================================================================
-- L1 Non-Strict Check
-- ============================================================================

/-- Check that L1 score for (u₁,w₁) is NOT strictly greater than for (u₂,w₂).
    Uses: score₁.hi ≤ score₂.lo (real value ≤ upper bound ≤ lower bound ≤ real value). -/
def checkL1ScoreNotGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (u₁ : U) (w₁ : W) (u₂ : U) (w₂ : W) : Bool :=
  let b₁ := computeL1ScoreBounds d u₁ w₁
  let b₂ := computeL1ScoreBounds d u₂ w₂
  b₁.hi ≤ b₂.lo

-- ============================================================================
-- Symbolic S1 Score Comparison (exact ℚ shortcuts)
-- ============================================================================

/-- Symbolic S1 score comparison: score(u₁) > score(u₂) via algebraic identity.

    Reduces S1 score comparisons to exact ℚ arithmetic by exploiting the
    structure of each scoring spec, bypassing interval approximation entirely.

    - **actionBased**: exp is monotone, so compare arguments directly (ℚ exact).
    - **beliefAction**: factor as `L0^α · exp(-α·c)`, then:
      - Equal L0: cancel L0^α → cost comparison (ℚ exact)
      - Equal cost: cancel exp → L0 comparison (ℚ exact)
      - Dominance: L0₁ ≥ L0₂ ∧ c₁ ≤ c₂ with one strict → score₁ > score₂
      - General: compare `L0₁^α / L0₂^α` against `expBounds(α·(c₁-c₂))`
    - **qudAction**: same as actionBased but on projected L0.
    - **beliefBased/qudBelief**: already exact (no exp), no shortcut needed.
    - **beliefWeighted**: no simple shortcut, fall back to intervals. -/
def trySymbolicS1ScoreGt {U W L : Type*} [Fintype W] [DecidableEq W] [DecidableEq L]
    (spec : S1ScoreSpec U W L)
    (meaning : L → U → W → ℚ) (α : ℚ)
    (l : L) (w : W) (u₁ u₂ : U) : Bool :=
  match spec with
  | .actionBased cost =>
    let p₁ := computeL0Rat meaning l u₁ w
    let p₂ := computeL0Rat meaning l u₂ w
    p₁ - cost u₁ > p₂ - cost u₂
  | .beliefAction cost =>
    let p₁ := computeL0Rat meaning l u₁ w
    let p₂ := computeL0Rat meaning l u₂ w
    let c₁ := cost u₁; let c₂ := cost u₂
    if p₁ = 0 then false
    else if p₂ = 0 then true
    else if p₁ = p₂ then c₁ < c₂
    else if c₁ = c₂ then p₁ > p₂
    else if p₁ ≥ p₂ && c₁ ≤ c₂ then p₁ > p₂ || c₁ < c₂
    else if p₁ ≤ p₂ && c₁ ≥ c₂ then false
    else
      -- General case: only exact when α is integer
      if α.den = 1 then
        let l0Ratio := (p₁ ^ α.num.toNat) / (p₂ ^ α.num.toNat)
        let expB := expBounds (α * (c₁ - c₂))
        l0Ratio > expB.hi
      else false
  | .qudAction cost project =>
    let l0 : W → ℚ := computeL0Rat meaning l u₁
    let proj₁ := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    let l0₂ : W → ℚ := computeL0Rat meaning l u₂
    let proj₂ := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0₂
    if proj₁ = 0 && proj₂ = 0 then false
    else if proj₂ = 0 then proj₁ > 0
    else if proj₁ = 0 then false
    else proj₁ - cost u₁ > proj₂ - cost u₂
  | .weightedBeliefAction infWeight bonus =>
    let p₁ := computeL0Rat meaning l u₁ w
    let p₂ := computeL0Rat meaning l u₂ w
    let b₁ := bonus u₁; let b₂ := bonus u₂
    if p₁ = 0 then false
    else if p₂ = 0 then true
    else if p₁ = p₂ then b₁ > b₂
    else if b₁ = b₂ then p₁ > p₂
    else if p₁ ≥ p₂ && b₁ ≥ b₂ then p₁ > p₂ || b₁ > b₂
    else if p₁ ≤ p₂ && b₁ ≤ b₂ then false
    else false
  | _ => false

/-- Symbolic S1 score comparison: ¬(score(u₁) > score(u₂)). -/
def trySymbolicS1ScoreNotGt {U W L : Type*} [Fintype W] [DecidableEq W] [DecidableEq L]
    (spec : S1ScoreSpec U W L)
    (meaning : L → U → W → ℚ) (α : ℚ)
    (l : L) (w : W) (u₁ u₂ : U) : Bool :=
  match spec with
  | .actionBased cost =>
    let p₁ := computeL0Rat meaning l u₁ w
    let p₂ := computeL0Rat meaning l u₂ w
    p₁ - cost u₁ ≤ p₂ - cost u₂
  | .beliefAction cost =>
    let p₁ := computeL0Rat meaning l u₁ w
    let p₂ := computeL0Rat meaning l u₂ w
    let c₁ := cost u₁; let c₂ := cost u₂
    if p₁ = 0 then true
    else if p₂ = 0 then false
    else if p₁ = p₂ then c₁ ≥ c₂
    else if c₁ = c₂ then p₁ ≤ p₂
    else if p₁ ≤ p₂ && c₁ ≥ c₂ then true
    else if p₁ ≥ p₂ && c₁ ≤ c₂ then p₁ = p₂ && c₁ = c₂
    else
      if α.den = 1 then
        let l0Ratio := (p₁ ^ α.num.toNat) / (p₂ ^ α.num.toNat)
        let expB := expBounds (α * (c₁ - c₂))
        l0Ratio ≤ expB.lo
      else false
  | .qudAction cost project =>
    let l0 : W → ℚ := computeL0Rat meaning l u₁
    let proj₁ := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    let l0₂ : W → ℚ := computeL0Rat meaning l u₂
    let proj₂ := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0₂
    if proj₁ = 0 then true
    else if proj₂ = 0 then false
    else proj₁ - cost u₁ ≤ proj₂ - cost u₂
  | .weightedBeliefAction _infWeight bonus =>
    let p₁ := computeL0Rat meaning l u₁ w
    let p₂ := computeL0Rat meaning l u₂ w
    let b₁ := bonus u₁; let b₂ := bonus u₂
    if p₁ = 0 then true
    else if p₂ = 0 then false
    else if p₁ = p₂ then b₁ ≤ b₂
    else if b₁ = b₂ then p₁ ≤ p₂
    else if p₁ ≤ p₂ && b₁ ≤ b₂ then true
    else if p₁ ≥ p₂ && b₁ ≥ b₂ then p₁ = p₂ && b₁ = b₂
    else false
  | _ => false

-- ============================================================================
-- S1 Checks
-- ============================================================================

/-- Check that S1 score for (l,w,u₁) is strictly greater than for (l,w,u₂).
    Same (l,w) → same denominator → score ordering = policy ordering.

    Tries symbolic comparison first (exact ℚ, no interval approximation),
    then falls back to interval bound separation. -/
def checkS1PolicyGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (l : d.Latent) (w : W) (u₁ u₂ : U) : Bool :=
  -- Try symbolic comparison first (exact ℚ, no interval approximation)
  if trySymbolicS1ScoreGt d.s1Spec d.meaning d.α l w u₁ u₂ then true
  else
    -- Fall back to interval comparison
    let b₁ := computeS1ScoreBounds d.s1Spec d.meaning d.α l w u₁
    let b₂ := computeS1ScoreBounds d.s1Spec d.meaning d.α l w u₂
    b₂.hi < b₁.lo

/-- Check that S1 score for (l,w,u₁) is NOT strictly greater than for (l,w,u₂).

    Tries symbolic comparison first, then falls back to interval bounds. -/
def checkS1PolicyNotGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (l : d.Latent) (w : W) (u₁ u₂ : U) : Bool :=
  if trySymbolicS1ScoreNotGt d.s1Spec d.meaning d.α l w u₁ u₂ then true
  else
    let b₁ := computeS1ScoreBounds d.s1Spec d.meaning d.α l w u₁
    let b₂ := computeS1ScoreBounds d.s1Spec d.meaning d.α l w u₂
    b₁.hi ≤ b₂.lo

-- ============================================================================
-- Soundness
-- ============================================================================

variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]

/-- Soundness: L1 score bounds contain the ℝ L1 score. -/
theorem computeL1ScoreBounds_sound (d : RSAConfigData U W) (u : U) (w : W) :
    let b := computeL1ScoreBounds d u w
    (↑b.lo : ℝ) ≤ d.toRSAConfig.L1agent.score u w ∧
    d.toRSAConfig.L1agent.score u w ≤ ↑b.hi := by
  sorry

/-- Master theorem: if `checkL1ScoreGt` returns true, then the ℝ L1 policies
    are strictly ordered (for same-utterance comparisons). -/
theorem l1_gt_of_check (d : RSAConfigData U W)
    (u : U) (w₁ w₂ : W)
    (h : checkL1ScoreGt d u w₁ u w₂ = true) :
    d.toRSAConfig.L1 u w₁ > d.toRSAConfig.L1 u w₂ := by
  sorry

/-- General score ordering theorem (allows different utterances). -/
theorem l1_score_gt_of_check (d : RSAConfigData U W)
    (u₁ : U) (w₁ : W) (u₂ : U) (w₂ : W)
    (h : checkL1ScoreGt d u₁ w₁ u₂ w₂ = true) :
    d.toRSAConfig.L1agent.score u₁ w₁ > d.toRSAConfig.L1agent.score u₂ w₂ := by
  sorry

/-- If checkL1ScoreNotGt returns true, then ¬(L1 u w₁ > L1 u w₂). -/
theorem l1_not_gt_of_check (d : RSAConfigData U W)
    (u : U) (w₁ w₂ : W)
    (h : checkL1ScoreNotGt d u w₁ u w₂ = true) :
    ¬(d.toRSAConfig.L1 u w₁ > d.toRSAConfig.L1 u w₂) := by
  sorry

/-- If checkS1PolicyGt returns true, then S1 l w u₁ > S1 l w u₂. -/
theorem s1_gt_of_check (d : RSAConfigData U W)
    (l : d.Latent) (w : W) (u₁ u₂ : U)
    (h : checkS1PolicyGt d l w u₁ u₂ = true) :
    d.toRSAConfig.S1 l w u₁ > d.toRSAConfig.S1 l w u₂ := by
  sorry

/-- If checkS1PolicyNotGt returns true, then ¬(S1 l w u₁ > S1 l w u₂). -/
theorem s1_not_gt_of_check (d : RSAConfigData U W)
    (l : d.Latent) (w : W) (u₁ u₂ : U)
    (h : checkS1PolicyNotGt d l w u₁ u₂ = true) :
    ¬(d.toRSAConfig.S1 l w u₁ > d.toRSAConfig.S1 l w u₂) := by
  sorry

-- ============================================================================
-- Extended Soundness (for auto-detected configs)
-- ============================================================================

/-- Bridge for auto-detected configs: if `d.toRSAConfig = cfg` (verified via
    `isDefEq` by the tactic) and the computable check passes on `d`, then
    `cfg` has the corresponding inequality.

    The `h_eq` hypothesis makes the theorem statement sound: the ℚ data in `d`
    must actually represent `cfg`. Once `l1_gt_of_check` is proved, the `_ext`
    version follows immediately from `h_eq ▸`. -/
theorem l1_gt_of_check_ext (cfg : RSA.RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (u : U) (w₁ w₂ : W)
    (h : checkL1ScoreGt d u w₁ u w₂ = true) :
    cfg.L1 u w₁ > cfg.L1 u w₂ :=
  h_eq ▸ l1_gt_of_check d u w₁ w₂ h

/-- Extended version for cross-utterance L1 score comparison. -/
theorem l1_score_gt_of_check_ext (cfg : RSA.RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (u₁ : U) (w₁ : W) (u₂ : U) (w₂ : W)
    (h : checkL1ScoreGt d u₁ w₁ u₂ w₂ = true) :
    cfg.L1agent.score u₁ w₁ > cfg.L1agent.score u₂ w₂ :=
  h_eq ▸ l1_score_gt_of_check d u₁ w₁ u₂ w₂ h

/-- Extended version for ¬(L1 gt). -/
theorem l1_not_gt_of_check_ext (cfg : RSA.RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (u : U) (w₁ w₂ : W)
    (h : checkL1ScoreNotGt d u w₁ u w₂ = true) :
    ¬(cfg.L1 u w₁ > cfg.L1 u w₂) :=
  h_eq ▸ l1_not_gt_of_check d u w₁ w₂ h

/-- Extended version for S1 gt.
    Requires both config equality and Latent type match. -/
theorem s1_gt_of_check_ext (cfg : RSA.RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (h_lat : d.Latent = cfg.Latent)
    (l : cfg.Latent) (w : W) (u₁ u₂ : U)
    (h : checkS1PolicyGt d (h_lat ▸ l) w u₁ u₂ = true) :
    cfg.S1 l w u₁ > cfg.S1 l w u₂ := by
  subst h_eq; exact s1_gt_of_check d (h_lat ▸ l) w u₁ u₂ h

/-- Extended version for ¬(S1 gt). -/
theorem s1_not_gt_of_check_ext (cfg : RSA.RSAConfig U W) (d : RSAConfigData U W)
    (h_eq : d.toRSAConfig = cfg)
    (h_lat : d.Latent = cfg.Latent)
    (l : cfg.Latent) (w : W) (u₁ u₂ : U)
    (h : checkS1PolicyNotGt d (h_lat ▸ l) w u₁ u₂ = true) :
    ¬(cfg.S1 l w u₁ > cfg.S1 l w u₂) := by
  subst h_eq; exact s1_not_gt_of_check d (h_lat ▸ l) w u₁ u₂ h

-- ============================================================================
-- Rational Coarsening (denominator control for nested interval pipelines)
-- ============================================================================

/-- Round q down (toward -∞) to nearest multiple of 1/2^n.
    Guarantees roundDownQ q n ≤ q. -/
def roundDownQ (q : ℚ) (n : ℕ) : ℚ :=
  let s : ℤ := 2 ^ n
  (⌊q * s⌋ : ℤ) / s

/-- Round q up (toward +∞) to nearest multiple of 1/2^n.
    Guarantees q ≤ roundUpQ q n. -/
def roundUpQ (q : ℚ) (n : ℕ) : ℚ :=
  let s : ℤ := 2 ^ n
  (⌈q * s⌉ : ℤ) / s

/-- Coarsen bounds to denominators of at most 2^n.
    Widens the interval slightly: lo rounds down, hi rounds up.
    This prevents denominator explosion in nested interval pipelines
    (e.g., logPoint on the output of divPos on S1 pipeline results). -/
def Bounds.coarsen (b : Bounds) (n : ℕ) : Bounds :=
  ⟨roundDownQ b.lo n, roundUpQ b.hi n⟩

-- ============================================================================
-- Fast Log via Atanh Series (for S2 pipeline)
-- ============================================================================

/-- Bounds for log(2). From log(2) = 0.693147180559945309...
    These bounds are verified to 10 decimal digits. -/
private def log2Lo : ℚ := 6931471805 / 10000000000
private def log2Hi : ℚ := 6931471806 / 10000000000

/-- Find k such that q · 2^k ∈ [1/2, 1]. Requires q > 0. -/
private def logReductionSteps (q : ℚ) : ℕ × Bool :=
  -- For q ∈ (0, 1]: find k ≥ 0 such that q·2^k ∈ [1/2, 1]
  -- For q > 1: find k ≥ 0 such that q/2^k ∈ [1/2, 1]
  if q ≤ 0 then (0, false)
  else if q ≤ 1 then
    -- Shift left until q·2^k ≥ 1/2
    let rec findK (k : ℕ) (v : ℚ) (fuel : ℕ) : ℕ :=
      match fuel with
      | 0 => k
      | fuel + 1 => if v ≥ 1/2 then k else findK (k + 1) (v * 2) fuel
    (findK 0 q 100, false)
  else
    -- Shift right until q/2^k ≤ 1
    let rec findKR (k : ℕ) (v : ℚ) (fuel : ℕ) : ℕ :=
      match fuel with
      | 0 => k
      | fuel + 1 => if v ≤ 1 then k else findKR (k + 1) (v / 2) fuel
    (findKR 0 q 100, true)

/-- Compute arctanh(y) partial sum: y + y³/3 + y⁵/5 +... + y^(2n-1)/(2n-1).
    All terms have the same sign as y, so the partial sum is monotone. -/
private def atanhPartialSum (y : ℚ) (n : ℕ) : ℚ :=
  let y2 := y * y
  let rec loop (k : ℕ) (yk : ℚ) (acc : ℚ) : ℕ → ℚ
    | 0 => acc
    | fuel + 1 =>
      if k ≥ n then acc
      else
        let term := yk / (2 * ↑k + 1 : ℚ)
        loop (k + 1) (yk * y2) (acc + term) fuel
  loop 0 y 0 (n + 1)

/-- Compute log(q) for 0 < q using argument reduction + atanh series.

    Algorithm:
    1. Reduce: find k so q·2^k ∈ [1/2, 1] (or q/2^k for q > 1)
    2. Compute log(q_reduced) = 2·arctanh((q_r-1)/(q_r+1))
       For q_r ∈ [1/2, 1]: |y| = |(q_r-1)/(q_r+1)| ≤ 1/3, series converges fast
    3. log(q) = log(q_r) ∓ k·log(2)

    With 15 terms: precision ≈ 2·(1/3)^31/(31·(1-1/9)) ≈ 3.5·10⁻¹⁶.
    Exact rational arithmetic throughout — no exp/log chains. -/
private def logPointAtan (q : ℚ) : ℚ × ℚ :=
  if q ≤ 0 then (-1000, -1000)
  else if q = 1 then (0, 0)
  else
    let (k, isLarge) := logReductionSteps q
    -- Reduced value in [1/2, 1]
    let qr := if isLarge then q / (2 ^ k : ℚ) else q * (2 ^ k : ℚ)
    let y := (qr - 1) / (qr + 1)
    let nTerms : ℕ := 15
    let partialSum := 2 * atanhPartialSum y nTerms
    -- Error bound: 2 · |y|^(2n+1) / ((2n+1) · (1 - y²))
    let yAbs := if y ≥ 0 then y else -y
    let y2 := y * y
    let errBound := 2 * (yAbs ^ (2 * nTerms + 1)) / ((2 * ↑nTerms + 1 : ℚ) * (1 - y2))
    -- log(qr) bounds: for qr ≤ 1 (y ≤ 0), series overestimates (closer to 0)
    let (logQrLo, logQrHi) :=
      if qr ≤ 1 then (partialSum - errBound, partialSum)
      else (partialSum, partialSum + errBound)
    -- Undo reduction: log(q) = log(qr) - k·log(2) (if q ≤ 1, we multiplied by 2^k)
    -- or log(q) = log(qr) + k·log(2) (if q > 1, we divided by 2^k)
    if isLarge then
      -- q > 1: log(q) = log(qr) + k·log(2)
      (logQrLo + ↑k * log2Lo, logQrHi + ↑k * log2Hi)
    else
      -- q ≤ 1: log(q) = log(qr) - k·log(2)
      (logQrLo - ↑k * log2Hi, logQrHi - ↑k * log2Lo)

/-- Log bounds over an interval, using atanh series.
    Monotonicity: log(lo) ≤ log(x) ≤ log(hi) for x ∈ [lo, hi]. -/
private def logBoundsFast (b : Bounds) : Bounds :=
  if b.hi ≤ 0 then ⟨-1000, -1000⟩
  else if b.lo ≤ 0 then
    let (_, hiLog) := logPointAtan b.hi
    ⟨-1000, hiLog⟩
  else
    let (loLog, _) := logPointAtan b.lo
    let (_, hiLog) := logPointAtan b.hi
    ⟨loLog, hiLog⟩

-- ============================================================================
-- S2 Pipeline: L1 Marginals → S2 Score → S2 Check
-- ============================================================================

/-- Bounds for log(b) where b is a nonneg Bounds interval.
    Uses logPoint on lo/hi (monotonicity of log). Returns [log(lo), log(hi)]
    when lo > 0; [-1000, log(hi)] when lo ≤ 0 (as a safe fallback). -/
def logBounds (b : Bounds) : Bounds :=
  if hhi : 0 < b.hi then
    if hlo : 0 < b.lo then
      ⟨(logPoint b.lo hlo).lo, (logPoint b.hi hhi).hi⟩
    else
      ⟨-1000, (logPoint b.hi hhi).hi⟩
  else ⟨-1000, -1000⟩

/-- Compute L1 normalization constant bounds: Σ_{w,l} prior(w) · prior(w,l) · S1(l,w,u). -/
def computeL1NormBounds {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (u : U) : Bounds :=
  let lo := Finset.univ.sum fun (w : W) =>
    d.worldPrior w * (Finset.univ.sum fun (l : d.Latent) =>
      d.latentPrior w l *
        (computeS1PolicyBounds d.s1Spec d.meaning d.α l w u).lo)
  let hi := Finset.univ.sum fun (w : W) =>
    d.worldPrior w * (Finset.univ.sum fun (l : d.Latent) =>
      d.latentPrior w l *
        (computeS1PolicyBounds d.s1Spec d.meaning d.α l w u).hi)
  ⟨lo, hi⟩

/-- Compute L1 state marginal bounds: P_L1(w|u) = L1_score(u,w) / Σ_w' L1_score(u,w').
    Returns bounds for the marginal probability of state w given utterance u. -/
def computeL1StateMarginalBounds {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (u : U) (w : W) : Bounds :=
  let score := computeL1ScoreBounds d u w
  let norm := computeL1NormBounds d u
  Bounds.divPos score norm

/-- Compute L1 latent marginal bounds: P_L1(l|u) = Σ_w prior(w)·prior(w,l)·S1(l,w,u) / norm. -/
def computeL1LatentMarginalBounds {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (u : U) (l : d.Latent) : Bounds :=
  let lo := Finset.univ.sum fun (w : W) =>
    d.worldPrior w * (d.latentPrior w l *
      (computeS1PolicyBounds d.s1Spec d.meaning d.α l w u).lo)
  let hi := Finset.univ.sum fun (w : W) =>
    d.worldPrior w * (d.latentPrior w l *
      (computeS1PolicyBounds d.s1Spec d.meaning d.α l w u).hi)
  let norm := computeL1NormBounds d u
  Bounds.divPos ⟨lo, hi⟩ norm

/-- Compute S2 utility bounds (before exp(α₂·U)).
    Returns bounds on the sum of S2 utility terms. -/
private def computeS2UtilityBounds {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (terms : List (RSA.S2UtilityTerm U W d.Latent))
    (w : W) (u : U) : Bounds :=
  -- Step 1: Compute L1 unnormalized scores for each world
  --   l1Score(w') = worldPrior(w') · Σ_l latentPrior(w',l) · S1(l,w',u)
  let l1ScoreLo : W → ℚ := fun w' =>
    d.worldPrior w' * (Finset.univ.sum fun (l : d.Latent) =>
      d.latentPrior w' l *
        (computeS1PolicyBounds d.s1Spec d.meaning d.α l w' u).lo)
  let l1ScoreHi : W → ℚ := fun w' =>
    d.worldPrior w' * (Finset.univ.sum fun (l : d.Latent) =>
      d.latentPrior w' l *
        (computeS1PolicyBounds d.s1Spec d.meaning d.α l w' u).hi)
  -- Step 2: Norm = Σ_w' l1Score(w')
  let normLo := Finset.univ.sum l1ScoreLo
  let normHi := Finset.univ.sum l1ScoreHi
  let norm : Bounds := ⟨normLo, normHi⟩
  -- Step 3: Coarsen L1 scores and norm to 30 binary digits before log.
  -- Without coarsening, S1 pipeline exp/log creates denominators > 10^1000.
  let l1ScoreCoarse : W → Bounds := fun w' =>
    (⟨l1ScoreLo w', l1ScoreHi w'⟩ : Bounds).coarsen 30
  let normCoarse := norm.coarsen 30
  -- Step 4: Evaluate each S2 utility term.
  -- Uses logBoundsFast on marginals directly (not log decomposition).
  -- The divPos→coarsen→logBoundsFast chain keeps denominators bounded:
  --   L1 scores (30-bit) → divPos (60-bit) → coarsen (30-bit) → logBoundsFast
  let evalTerm : RSA.S2UtilityTerm U W d.Latent → Bounds := fun t =>
    match t with
    | .logStateMarginal weight =>
      let marg := (Bounds.divPos (l1ScoreCoarse w) normCoarse).coarsen 30
      (Bounds.exact weight).mul (logBoundsFast marg)
    | .expectedValue weight value =>
      -- Sign-aware multiplication: when value(w') < 0, multiplying by
      -- divPos.lo gives the UPPER bound (not lower). Handle both signs.
      let evLo := Finset.univ.sum fun (w' : W) =>
        let marg := Bounds.divPos (l1ScoreCoarse w') normCoarse
        if value w' ≥ 0 then value w' * marg.lo else value w' * marg.hi
      let evHi := Finset.univ.sum fun (w' : W) =>
        let marg := Bounds.divPos (l1ScoreCoarse w') normCoarse
        if value w' ≥ 0 then value w' * marg.hi else value w' * marg.lo
      (Bounds.exact weight).mul ⟨evLo, evHi⟩
    | .logLatentMarginal weight target =>
      let latLo := Finset.univ.sum fun (w' : W) =>
        d.worldPrior w' * (d.latentPrior w' target *
          (computeS1PolicyBounds d.s1Spec d.meaning d.α target w' u).lo)
      let latHi := Finset.univ.sum fun (w' : W) =>
        d.worldPrior w' * (d.latentPrior w' target *
          (computeS1PolicyBounds d.s1Spec d.meaning d.α target w' u).hi)
      let latCoarse := (⟨latLo, latHi⟩ : Bounds).coarsen 30
      let marg := (Bounds.divPos latCoarse normCoarse).coarsen 30
      (Bounds.exact weight).mul (logBoundsFast marg)
    | .constant fn =>
      Bounds.exact (fn u)
  terms.foldl (fun acc t => acc.add (evalTerm t)) Bounds.zero

/-- Compute S2 score bounds, dispatching on S2ScoreSpec.

    For `utilityMaximizing`: computes L1 marginals inline, evaluating S1
    policies once and reusing the results for all terms. -/
def computeS2ScoreBounds {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (spec : RSA.S2ScoreSpec U W d.Latent)
    (w : W) (u : U) : Bounds :=
  match spec with
  | .endorsement =>
    computeL1ScoreBounds d u w
  | .utilityMaximizing α₂ terms =>
    let utility := computeS2UtilityBounds d terms w u
    let scaled : Bounds := ⟨α₂ * utility.lo, α₂ * utility.hi⟩
    expIntervalBounds scaled

/-- Check that S2 score for (w,u₁) is strictly greater than for (w,u₂).
    For `utilityMaximizing`, compares utilities directly (exp is monotone). -/
def checkS2ScoreGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (w : W) (u₁ u₂ : U) : Bool :=
  match d.s2Spec with
  | none => false
  | some spec => match spec with
    | .endorsement =>
      let b₁ := computeS2ScoreBounds d spec w u₁
      let b₂ := computeS2ScoreBounds d spec w u₂
      b₂.hi < b₁.lo
    | .utilityMaximizing _α₂ terms =>
      -- Compare utilities directly: exp(α₂·U₁) > exp(α₂·U₂) iff U₁ > U₂
      -- This avoids the final exp step, removing interval widening.
      let u₁_util := computeS2UtilityBounds d terms w u₁
      let u₂_util := computeS2UtilityBounds d terms w u₂
      u₂_util.hi < u₁_util.lo

/-- Soundness: if checkS2ScoreGt returns true, then S2Utility u₁ > S2Utility u₂.
    The ℚ interval pipeline bounds the ℝ S2 utility; separation of bounds implies
    strict inequality. -/
theorem s2_utility_gt_of_check (d : RSAConfigData U W)
    (w : W) (u₁ u₂ : U)
    (h : checkS2ScoreGt d w u₁ u₂ = true) :
    d.S2Utility w u₁ > d.S2Utility w u₂ := by
  sorry

end RSA.Verify
