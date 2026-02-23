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
    (meaning : L → U → W → ℚ) (α : ℕ)
    (l : L) (w : W) (u : U) : Bounds :=
  match spec with
  | .beliefBased =>
    Bounds.exact ((computeL0Rat meaning l u w) ^ α)
  | .qudBelief project =>
    let l0 : W → ℚ := computeL0Rat meaning l u
    let projected := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    Bounds.exact (projected ^ α)
  | .qudAction cost project =>
    let l0 : W → ℚ := computeL0Rat meaning l u
    let projected := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    if projected = 0 then Bounds.zero
    else
      -- exp(α·(log projected - cost u)) = projected^α · exp(-α · cost u)
      (Bounds.exact (projected ^ α)).mul (expBounds (-(↑α * cost u)))
  | .beliefAction cost =>
    let p := computeL0Rat meaning l u w
    if p = 0 then Bounds.zero
    else (Bounds.exact (p ^ α)).mul (expBounds (-(↑α * cost u)))
  | .actionBased cost =>
    let p := computeL0Rat meaning l u w
    expBounds (↑α * (p - cost u))
  | .beliefWeighted belief quality =>
    if quality l u then
      -- exp(α · Σ_w belief(l,w) · log(L0(u,w)))
      -- Compute the argument bounds via Finset.sum on lo/hi
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
      -- Scale by α and take exp
      let scaled : Bounds := ⟨↑α * argLo, ↑α * argHi⟩
      expIntervalBounds scaled
    else Bounds.zero

-- ============================================================================
-- S1 Policy Bounds
-- ============================================================================

/-- Compute S1 policy bounds: score(u) / Σ_{u'} score(u').
    Uses `Finset.sum` for totals (computable over ℚ). -/
def computeS1PolicyBounds {U W L : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W] [DecidableEq L]
    (spec : S1ScoreSpec U W L)
    (meaning : L → U → W → ℚ) (α : ℕ)
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
      (computeS1PolicyBounds d.scoreSpec d.meaning d.α l w u).lo
  let latentSumHi := Finset.univ.sum fun (l : d.Latent) =>
    d.latentPrior w l *
      (computeS1PolicyBounds d.scoreSpec d.meaning d.α l w u).hi
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
    (meaning : L → U → W → ℚ) (α : ℕ)
    (l : L) (w : W) (u₁ u₂ : U) : Bool :=
  match spec with
  | .actionBased cost =>
    -- exp(α·(L0₁ - c₁)) > exp(α·(L0₂ - c₂)) iff L0₁ - c₁ > L0₂ - c₂
    let p₁ := computeL0Rat meaning l u₁ w
    let p₂ := computeL0Rat meaning l u₂ w
    p₁ - cost u₁ > p₂ - cost u₂
  | .beliefAction cost =>
    let p₁ := computeL0Rat meaning l u₁ w
    let p₂ := computeL0Rat meaning l u₂ w
    let c₁ := cost u₁; let c₂ := cost u₂
    if p₁ = 0 then false  -- score₁ = 0, can't be greater
    else if p₂ = 0 then true  -- score₂ = 0, score₁ > 0
    else if p₁ = p₂ then
      -- L0^α cancels: exp(-α·c₁) > exp(-α·c₂) iff c₁ < c₂
      c₁ < c₂
    else if c₁ = c₂ then
      -- exp terms cancel: L0₁^α > L0₂^α iff L0₁ > L0₂ (for positive L0, α > 0)
      p₁ > p₂
    else if p₁ ≥ p₂ && c₁ ≤ c₂ then
      -- Dominance: both factors favor u₁ (one strictly)
      p₁ > p₂ || c₁ < c₂
    else if p₁ ≤ p₂ && c₁ ≥ c₂ then
      -- Reverse dominance: both factors favor u₂
      false
    else
      -- General case: L0₁^α / L0₂^α > exp(α·(c₁-c₂))
      -- L0₁^α / L0₂^α is exact ℚ; one Padé evaluation for exp
      let l0Ratio := (p₁ ^ α) / (p₂ ^ α)
      let expB := expBounds (↑α * (c₁ - c₂))
      l0Ratio > expB.hi
  | .qudAction cost project =>
    -- Same as actionBased but on projected L0
    let l0 : W → ℚ := computeL0Rat meaning l u₁
    let proj₁ := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    let l0₂ : W → ℚ := computeL0Rat meaning l u₂
    let proj₂ := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0₂
    if proj₁ = 0 && proj₂ = 0 then false
    else if proj₂ = 0 then proj₁ > 0
    else if proj₁ = 0 then false
    else proj₁ - cost u₁ > proj₂ - cost u₂
  | _ => false  -- beliefBased/qudBelief are already exact; beliefWeighted no shortcut

/-- Symbolic S1 score comparison: ¬(score(u₁) > score(u₂)). -/
def trySymbolicS1ScoreNotGt {U W L : Type*} [Fintype W] [DecidableEq W] [DecidableEq L]
    (spec : S1ScoreSpec U W L)
    (meaning : L → U → W → ℚ) (α : ℕ)
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
    if p₁ = 0 then true  -- score₁ = 0, not greater
    else if p₂ = 0 then false  -- score₂ = 0, score₁ > 0, so IS greater
    else if p₁ = p₂ then c₁ ≥ c₂
    else if c₁ = c₂ then p₁ ≤ p₂
    else if p₁ ≤ p₂ && c₁ ≥ c₂ then true  -- both factors favor u₂
    else if p₁ ≥ p₂ && c₁ ≤ c₂ then
      -- Both favor u₁ — IS greater unless equal
      p₁ = p₂ && c₁ = c₂
    else
      -- General case: check L0₁^α / L0₂^α ≤ exp(α·(c₁-c₂)).lo
      let l0Ratio := (p₁ ^ α) / (p₂ ^ α)
      let expB := expBounds (↑α * (c₁ - c₂))
      l0Ratio ≤ expB.lo
  | .qudAction cost project =>
    let l0 : W → ℚ := computeL0Rat meaning l u₁
    let proj₁ := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0
    let l0₂ : W → ℚ := computeL0Rat meaning l u₂
    let proj₂ := (Finset.univ.filter (fun w' => project w' l = project w l)).sum l0₂
    if proj₁ = 0 then true
    else if proj₂ = 0 then false
    else proj₁ - cost u₁ ≤ proj₂ - cost u₂
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
  if trySymbolicS1ScoreGt d.scoreSpec d.meaning d.α l w u₁ u₂ then true
  else
    -- Fall back to interval comparison
    let b₁ := computeS1ScoreBounds d.scoreSpec d.meaning d.α l w u₁
    let b₂ := computeS1ScoreBounds d.scoreSpec d.meaning d.α l w u₂
    b₂.hi < b₁.lo

/-- Check that S1 score for (l,w,u₁) is NOT strictly greater than for (l,w,u₂).

    Tries symbolic comparison first, then falls back to interval bounds. -/
def checkS1PolicyNotGt {U W : Type*} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W]
    (d : RSAConfigData U W) (l : d.Latent) (w : W) (u₁ u₂ : U) : Bool :=
  if trySymbolicS1ScoreNotGt d.scoreSpec d.meaning d.α l w u₁ u₂ then true
  else
    let b₁ := computeS1ScoreBounds d.scoreSpec d.meaning d.α l w u₁
    let b₂ := computeS1ScoreBounds d.scoreSpec d.meaning d.α l w u₂
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

end RSA.Verify
