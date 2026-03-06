import Linglib.Theories.Semantics.Degree.Core
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Phenomena.Negation.FlexibleNegation

/-!
# @cite{tessler-franke-2019}: Not Unreasonable
@cite{tessler-franke-2019}

Why two negatives don't make a positive.

## Model

RSA with lexical uncertainty over morphological negation "un-".
The listener L1 reasons about why the speaker chose a costly negated
form, inferring the intended degree of happiness.

**Key distinction**:
- **Contradictory**: ¬H(x) = x ≤ θ₁ (complement, no gap)
- **Contrary**: H̃(x) = x < θ₂ where θ₂ ≤ θ₁ (polar opposite, gap)

The gap region θ₂ ≤ x ≤ θ₁ is "not unhappy" but NOT "happy".

## Equations

    L0(x | u, θ₁, θ₂, L) ∝ ⟦u⟧(x, θ₁, θ₂, L)
    S1(u | x, θ₁, θ₂, L) ∝ L0(x | u)^α · exp(−C(u))
    L1(x, θ₁, θ₂, L | u) ∝ S1(u | x, θ₁, θ₂, L) · P(x) · P(θ₁) · P(θ₂) · P(L)

## Parameters

- Scale: 5-point happiness (`Degree 4`), discretizing P(x) = Uniform(0,1)
- Utterances: happy, unhappy, not happy, not unhappy (4 adjectival forms)
- α = 1, P(x) = P(θ₁) = P(θ₂) = P(L) = Uniform
- Costs: C(happy) = 0, C(unhappy) = 2, C(not happy) = 3, C(not unhappy) = 5

## Verified Predictions

| # | Prediction | Theorem |
|---|-----------|---------|
| 1 | "happy" → high degree | `happy_implies_high` |
| 2 | "unhappy" → low degree | `unhappy_implies_low` |
| 3 | "not happy" → low degree | `not_happy_implies_low` |
| 4 | "not unhappy" rules out negative | `not_unhappy_above_negative` |
| 5 | "not unhappy" ≠ "happy" (gap) | `not_unhappy_prefers_gap` |
| 6 | "not unhappy" > "not happy" | `not_unhappy_more_positive_than_not_happy` |
-/

set_option autoImplicit false

namespace Phenomena.Negation.Studies.TesslerFranke2020

open Core.Scale (Degree Threshold deg thr Degree.toNat Threshold.toNat)
open Semantics.Degree (positiveMeaning negativeMeaning)
open Real (rpow rpow_nonneg exp exp_pos)

-- ============================================================================
-- § 1. Domain Types
-- ============================================================================

/-- Happiness degree: 0 (miserable) to 4 (ecstatic). -/
abbrev HappinessDeg := Degree 4

instance : NeZero (4 : Nat) := ⟨by omega⟩

/-- Threshold values 0–3, used for both θ₁ (positive) and θ₂ (contrary). -/
abbrev HThreshold := Threshold 4

-- ============================================================================
-- § 2. Utterances and Lexicon
-- ============================================================================

inductive Utterance where
  | happy       -- "is happy"
  | notHappy    -- "is not happy"
  | unhappy     -- "is unhappy"
  | notUnhappy  -- "is not unhappy"
  deriving Repr, DecidableEq, BEq, Fintype

/-- Lexicon for morphological negation "un-":
    contrary (polar opposite with gap) vs contradictory (complement).
    Syntactic negation "not" is always contradictory in this model. -/
inductive NegLexicon where
  | contrary
  | contradictory
  deriving Repr, DecidableEq, BEq, Fintype

-- ============================================================================
-- § 3. Latent State
-- ============================================================================

/-- Joint latent state: (θ₁, θ₂, L).
    - θ₁: positive threshold ("happy" = x > θ₁)
    - θ₂: contrary threshold ("unhappy" contrary = x < θ₂)
    - L: how "un-" is interpreted
    4 × 4 × 2 = 32 latent states. -/
@[reducible] def LatentState := HThreshold × HThreshold × NegLexicon

-- ============================================================================
-- § 4. Semantics (grounded in Semantics.Degree)
-- ============================================================================

/-- Utterance meaning parameterized by thresholds and lexicon.

    Uses `positiveMeaning` and `negativeMeaning` from `Semantics.Degree.Core`,
    grounding the model in shared scalar adjective semantics.

    - "happy": x > θ₁
    - "not happy": x ≤ θ₁ (contradictory, always)
    - "unhappy": L = contrary → x < θ₂; L = contradictory → x ≤ θ₁
    - "not unhappy": L = contrary → x ≥ θ₂; L = contradictory → x > θ₁ -/
def utteranceMeaning (θ₁ θ₂ : HThreshold) (L : NegLexicon)
    (u : Utterance) (d : HappinessDeg) : Bool :=
  match u with
  | .happy => positiveMeaning d θ₁            -- d > θ₁
  | .notHappy => !positiveMeaning d θ₁        -- d ≤ θ₁ (contradictory)
  | .unhappy => match L with
    | .contrary => negativeMeaning d θ₂        -- d < θ₂
    | .contradictory => !positiveMeaning d θ₁  -- d ≤ θ₁
  | .notUnhappy => match L with
    | .contrary => !negativeMeaning d θ₂       -- d ≥ θ₂
    | .contradictory => positiveMeaning d θ₁   -- d > θ₁

-- ============================================================================
-- § 5. Utterance Costs
-- ============================================================================

/-- Utterance cost: morphological complexity.

    C(un-) = 2, C(not) = 3, combined additively.
    Cost discount d(u) = exp(−C(u)) enters S1 scoring. -/
def utteranceCost (u : Utterance) : ℚ :=
  match u with
  | .happy => 0
  | .unhappy => 2      -- un-
  | .notHappy => 3     -- not
  | .notUnhappy => 5   -- not + un-

-- ============================================================================
-- § 6. RSAConfig
-- ============================================================================

/-- ℝ-valued meaning: 1 if true, 0 if false. -/
private def meaningR (l : LatentState) (u : Utterance) (d : HappinessDeg) : ℝ :=
  if utteranceMeaning l.1 l.2.1 l.2.2 u d then (1 : ℝ) else 0

private theorem meaningR_nonneg (l : LatentState) (u : Utterance)
    (d : HappinessDeg) : 0 ≤ meaningR l u d := by
  simp only [meaningR]; split <;> norm_num

/-- RSA configuration for the Flexible Negation model.

    - Latent: (θ₁, θ₂, L) — threshold pair and lexicon (32 states)
    - Meaning: Boolean semantics cast to ℝ
    - S1 score: rpow(L0, α) · exp(−C(u)) (belief-based with cost)
    - α = 1, priors: all uniform -/
@[reducible]
noncomputable def negationCfg : RSA.RSAConfig Utterance HappinessDeg where
  Latent := LatentState
  meaning _ l u d := meaningR l u d
  meaning_nonneg _ l u d := meaningR_nonneg l u d
  s1Score l0 α _ w u := rpow (l0 u w) α * exp (-(utteranceCost u : ℝ))
  s1Score_nonneg l0 α _ w u hl _ :=
    mul_nonneg (rpow_nonneg (hl u w) α) (exp_pos _).le
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

-- ============================================================================
-- § 7. Semantic Properties
-- ============================================================================

/-- "happy" excludes the gap region: with θ₁ = 3 and θ₂ = 2,
    degrees 2 and 3 are NOT happy. -/
theorem happy_excludes_gap :
    ∀ d : HappinessDeg,
      utteranceMeaning (thr 3) (thr 2) .contrary .happy d = true →
      negativeMeaning d (thr 2) = false := by
  native_decide

/-- "not unhappy" (contrary) includes the gap: degrees 2 and 3 satisfy
    "not unhappy" under contrary lexicon with θ₂ = 2. -/
theorem not_unhappy_includes_gap :
    ∃ d : HappinessDeg,
      utteranceMeaning (thr 3) (thr 2) .contrary .notUnhappy d = true ∧
      utteranceMeaning (thr 3) (thr 2) .contrary .happy d = false := by
  native_decide

-- ============================================================================
-- § 8. RSA Predictions
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- "happy" implies high degree: degree 4 > degree 2 given "happy". -/
theorem happy_implies_high :
    negationCfg.L1 .happy (deg 4) > negationCfg.L1 .happy (deg 2) := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- "unhappy" implies low degree: degree 0 > degree 4 given "unhappy". -/
theorem unhappy_implies_low :
    negationCfg.L1 .unhappy (deg 0) > negationCfg.L1 .unhappy (deg 4) := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- "not unhappy" rules out strongly negative: degree 2 > degree 0. -/
theorem not_unhappy_above_negative :
    negationCfg.L1 .notUnhappy (deg 2) > negationCfg.L1 .notUnhappy (deg 0) := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- THE KEY PREDICTION: "not unhappy" ≠ "happy".
    Given "not unhappy", the gap region (degree 2) is MORE likely than
    the top of the scale (degree 4). A rational speaker would say "happy"
    (cheap) to describe degree 4, reserving the expensive "not unhappy"
    for the gap region where "happy" is false. -/
theorem not_unhappy_prefers_gap :
    negationCfg.L1 .notUnhappy (deg 2) > negationCfg.L1 .notUnhappy (deg 4) := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- "not happy" implies low degree: degree 0 > degree 4 given "not happy".
    The negated positive peaks in the negative region, like "unhappy". -/
theorem not_happy_implies_low :
    negationCfg.L1 .notHappy (deg 0) > negationCfg.L1 .notHappy (deg 4) := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- "not unhappy" is more positive than "not happy":
    degree 3 is more likely given "not unhappy" than given "not happy".
    This captures the ordering: not happy < not unhappy < happy. -/
theorem not_unhappy_more_positive_than_not_happy :
    negationCfg.L1 .notUnhappy (deg 3) > negationCfg.L1 .notHappy (deg 3) := by
  rsa_predict

-- ============================================================================
-- § 9. Connection to FlexibleNegation Data
-- ============================================================================

/-! The predictions verify the empirical patterns from
`Phenomena.Negation.FlexibleNegation`:

1. `prediction_double_neg_gap` — "not unhappy" has gap probability:
   `not_unhappy_prefers_gap` shows degree 2 (gap) > degree 4 (top).

2. `prediction_unhappy_contrary` — "unhappy" prefers contrary:
   `not_unhappy_includes_gap` shows the semantic basis (gap exists
   under contrary lexicon).

The ordering `happy_implies_high` + `not_unhappy_prefers_gap` together
show that "not unhappy" ≠ "happy": they peak in different regions. -/

end Phenomena.Negation.Studies.TesslerFranke2020
