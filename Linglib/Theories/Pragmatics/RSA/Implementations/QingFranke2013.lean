/-
# Qing & Franke (2013) @cite{qing-franke-2013}

"Variations on a Bayesian Theme: Comparing Bayesian Models of Referential Reasoning"

This paper decomposes Bayesian pragmatic models along three orthogonal
dimensions: **belief** (what the speaker assumes about the listener),
**goal** (what the speaker optimizes for), and **action** (how the speaker
turns utility into choices via softmax). The decomposition yields a family
of models that includes Frank & Goodman (2012) as one instance.

## Speaker Models (σ_{xy})

Two dimensions, each binary:

| Dimension | Options | Description |
|-----------|---------|-------------|
| Goal (x)  | b = belief-oriented | score = L0(t\|m)^α · exp(-α·C(m)) |
|           | a = action-oriented | score = exp(α · (L0(t\|m) - C(m))) |
| Belief (y)| U = uniform | L0 assumes uniform prior over referents |
|           | S = salience | L0 weighted by perceptual salience S(t) |

This gives 4 speaker models: σ_{bU}, σ_{aU}, σ_{bS}, σ_{aS}.

## Listener Models (ρ)

- ρ_{bv}(σ) : belief-oriented listener, prior v ∈ {U, S}, Bayesian update
- ρ_{av}(σ) : action-oriented listener, softmax over ρ_{bv}

## Key Finding

σ_{bU} (= standard RSA) and σ_{aU} best explain speaker data. The salience
prior helps listener predictions but not speaker predictions. The
action-oriented listener (softmax over Bayesian posterior) provides an
additional degree of freedom for fitting listener data.

## API Stress Test

This file tests that `RSAConfig` supports:
1. Different `s1Score` functions (belief vs action goals)
2. Different `meaning` functions (uniform vs salience-weighted L0)
3. Utterance cost incorporated into `s1Score`
4. Different `worldPrior` for the listener
5. Composable extensions (action-oriented listener via softmax over L1)

## References

- Qing & Franke (2013). Variations on a Bayesian Theme.
- Frank & Goodman (2012). Predicting Pragmatic Reasoning in Language Games.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Config
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RSA.QingFranke2013

open RSA BigOperators Core Real

-- ============================================================================
-- Domain Types
-- ============================================================================

/-- Structural roles of the three objects in the reference game context.

Each context has a square and a circle sharing the same color, plus another
circle of a different color. E.g., {green_square, green_circle, blue_circle}. -/
inductive Object where
  | uniqueShape  -- the square: unique shape, shared color
  | uniqueColor  -- e.g., blue circle: shared shape, unique color
  | bothShared   -- e.g., green circle: both features shared
  deriving Repr, DecidableEq, BEq

instance : Fintype Object where
  elems := {.uniqueShape, .uniqueColor, .bothShared}
  complete := fun o => by cases o <;> decide

instance : Nonempty Object := ⟨.uniqueShape⟩

/-- The four feature words usable as referring expressions.

- uniqueShapeWord ("square"): applies only to uniqueShape
- sharedShapeWord ("circle"): applies to uniqueColor and bothShared
- uniqueColorWord ("blue"): applies only to uniqueColor
- sharedColorWord ("green"): applies to uniqueShape and bothShared -/
inductive Utterance where
  | uniqueShapeWord | sharedShapeWord | uniqueColorWord | sharedColorWord
  deriving Repr, DecidableEq, BEq

instance : Fintype Utterance where
  elems := {.uniqueShapeWord, .sharedShapeWord, .uniqueColorWord, .sharedColorWord}
  complete := fun u => by cases u <;> decide

instance : Nonempty Utterance := ⟨.uniqueShapeWord⟩

-- ============================================================================
-- Semantics
-- ============================================================================

/-- Boolean semantics: ⟦utterance⟧(object).

Each unique-feature word applies to exactly 1 object;
each shared-feature word applies to exactly 2 objects. -/
def Utterance.appliesTo : Utterance → Object → Bool
  | .uniqueShapeWord, .uniqueShape => true
  | .sharedShapeWord, .uniqueColor => true
  | .sharedShapeWord, .bothShared  => true
  | .uniqueColorWord, .uniqueColor => true
  | .sharedColorWord, .uniqueShape => true
  | .sharedColorWord, .bothShared  => true
  | _, _ => false

-- ============================================================================
-- Cost Structure
-- ============================================================================

/-- Adjective cost: shape words (nouns) are free, color words (adjectives) cost c.

From Q&F Eq. (11): Cost(m) = c if m is an adjective, 0 otherwise.
Positive c penalizes color words; negative c penalizes shape words. -/
def adjCost (c : ℝ) : Utterance → ℝ
  | .uniqueShapeWord | .sharedShapeWord => 0
  | .uniqueColorWord | .sharedColorWord => c

-- ============================================================================
-- Speaker Utility Variants (Goal Dimension)
-- ============================================================================

/-- Belief-oriented S1 score with cost: L0(w|u)^α · exp(-α · cost(u)).

Uses rpow so that false utterances (L0 = 0) correctly get score 0.
Equivalent to exp(α · (log L0(w|u) - cost(u))) when L0 > 0. (Q&F Eq. 10) -/
noncomputable def beliefGoalScore (cost : Utterance → ℝ) :
    (Utterance → Object → ℝ) → ℝ → Unit → Object → Utterance → ℝ :=
  fun l0 α _ w u => rpow (l0 u w) α * exp (-α * cost u)

theorem beliefGoalScore_nonneg (cost : Utterance → ℝ) :
    ∀ (l0 : Utterance → Object → ℝ) (α : ℝ) (l : Unit) (w : Object) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ beliefGoalScore cost l0 α l w u :=
  fun _ α _ w u hl _ =>
    mul_nonneg (rpow_nonneg (hl u w) α) (le_of_lt (exp_pos _))

/-- Action-oriented S1 score with cost: exp(α · (L0(w|u) - cost(u))).

The speaker maximizes the listener's raw probability of choosing the correct
referent, rather than log-probability. (Q&F Eq. 9) -/
noncomputable def actionGoalScore (cost : Utterance → ℝ) :
    (Utterance → Object → ℝ) → ℝ → Unit → Object → Utterance → ℝ :=
  fun l0 α _ w u => exp (α * (l0 u w - cost u))

theorem actionGoalScore_nonneg (cost : Utterance → ℝ) :
    ∀ (l0 : Utterance → Object → ℝ) (α : ℝ) (l : Unit) (w : Object) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ actionGoalScore cost l0 α l w u :=
  fun _ _ _ _ _ _ _ => le_of_lt (exp_pos _)

-- ============================================================================
-- Parametric RSAConfig Constructor
-- ============================================================================

/-- Construct a Q&F RSAConfig from:

- `speakerPrior`: what the speaker believes about L0's prior (1 = uniform, salience = S)
- `s1`: S1 scoring rule (beliefGoalScore or actionGoalScore)
- `listenerPrior`: what L1 uses as world prior (1 = uniform, salience = S)

The speaker's belief dimension and the listener's prior are independent—
the speaker may assume a uniform L0 while the listener uses salience, or
vice versa. This decoupling is a key feature of the RSAConfig API. -/
noncomputable def mkConfig
    (speakerPrior : Object → ℝ) (sp_nonneg : ∀ w, 0 ≤ speakerPrior w)
    (s1 : (Utterance → Object → ℝ) → ℝ → Unit → Object → Utterance → ℝ)
    (s1_nn : ∀ (l0 : Utterance → Object → ℝ) (α : ℝ) (l : Unit) (w : Object) (u : Utterance),
      (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ s1 l0 α l w u)
    (listenerPrior : Object → ℝ) (lp_nonneg : ∀ w, 0 ≤ listenerPrior w)
    (αS : ℝ) (hα : 0 < αS) : RSAConfig Utterance Object where
  meaning _ u w := if u.appliesTo w then speakerPrior w else 0
  meaning_nonneg _ _ w := by
    split
    · exact sp_nonneg w
    · exact le_refl 0
  s1Score := s1
  s1Score_nonneg := s1_nn
  worldPrior := listenerPrior
  worldPrior_nonneg := lp_nonneg
  α := αS
  α_pos := hα
  latentPrior_nonneg _ := by positivity

-- ============================================================================
-- Speaker Models
-- ============================================================================

/-- Uniform speaker prior: the speaker assumes L0 has no object bias. -/
def uniformPrior : Object → ℝ := fun _ => 1

theorem uniformPrior_nonneg : ∀ w, 0 ≤ uniformPrior w :=
  fun _ => le_of_lt one_pos

/-- σ_{bU}: Belief-oriented speaker, uniform L0.

This is standard RSA (Frank & Goodman 2012) with utterance costs.
S1 score = L0(w|u)^α · exp(-α · cost(u)), where L0 is uniform. -/
noncomputable def σ_bU (αS : ℝ) (hα : 0 < αS) (cost : Utterance → ℝ) :
    RSAConfig Utterance Object :=
  mkConfig uniformPrior uniformPrior_nonneg
    (beliefGoalScore cost) (beliefGoalScore_nonneg cost)
    uniformPrior uniformPrior_nonneg αS hα

/-- σ_{aU}: Action-oriented speaker, uniform L0.

S1 score = exp(α · (L0(w|u) - cost(u))), where L0 is uniform. -/
noncomputable def σ_aU (αS : ℝ) (hα : 0 < αS) (cost : Utterance → ℝ) :
    RSAConfig Utterance Object :=
  mkConfig uniformPrior uniformPrior_nonneg
    (actionGoalScore cost) (actionGoalScore_nonneg cost)
    uniformPrior uniformPrior_nonneg αS hα

/-- σ_{bS}: Belief-oriented speaker, salience-weighted L0.

The speaker assumes L0 weights worlds by perceptual salience:
L0(t|m) ∝ S(t) · ⟦m⟧(t). Speaker score = L0(w|u)^α · exp(-α · cost). -/
noncomputable def σ_bS (αS : ℝ) (hα : 0 < αS) (cost : Utterance → ℝ)
    (sal : Object → ℝ) (sal_nn : ∀ w, 0 ≤ sal w) :
    RSAConfig Utterance Object :=
  mkConfig sal sal_nn
    (beliefGoalScore cost) (beliefGoalScore_nonneg cost)
    uniformPrior uniformPrior_nonneg αS hα

/-- σ_{aS}: Action-oriented speaker, salience-weighted L0.

Same salience-weighted L0 as σ_{bS}, but speaker score = exp(α · (L0(w|u) - cost)). -/
noncomputable def σ_aS (αS : ℝ) (hα : 0 < αS) (cost : Utterance → ℝ)
    (sal : Object → ℝ) (sal_nn : ∀ w, 0 ≤ sal w) :
    RSAConfig Utterance Object :=
  mkConfig sal sal_nn
    (actionGoalScore cost) (actionGoalScore_nonneg cost)
    uniformPrior uniformPrior_nonneg αS hα

-- ============================================================================
-- Listener Models
-- ============================================================================

/-- Action-oriented listener: ρ_{av}(t|m) = softmax(ρ_{bv}(·|m), λ_L)(t).

Applies a second softmax to the belief-oriented L1 posterior (Q&F Eq. 14).
This models a listener who soft-maximizes over Bayesian beliefs rather
than reporting beliefs directly.

The RSAConfig API doesn't directly support this, so it's defined as a
composable extension—demonstrating that the API is open for extension
without modification. -/
noncomputable def L1_action (cfg : RSAConfig Utterance Object)
    (αL : ℝ) (u : Utterance) (w : Object) : ℝ :=
  softmax (cfg.L1 u) αL w

-- ============================================================================
-- Experimental Data
-- ============================================================================

/-- Salience data from Table 2, salience condition (N = 240).

Blue circle (uniqueColor) is most salient; green circle (bothShared) least. -/
def empiricalSalience : Object → ℝ
  | .uniqueShape => 71
  | .uniqueColor => 139
  | .bothShared  => 30

theorem empiricalSalience_nonneg : ∀ w, 0 ≤ empiricalSalience w := by
  intro w; cases w <;> norm_num [empiricalSalience]

-- ============================================================================
-- Structural Properties
-- ============================================================================

/-- uniqueShapeWord uniquely identifies uniqueShape. -/
theorem uniqueShapeWord_unique :
    Utterance.appliesTo .uniqueShapeWord .uniqueShape = true ∧
    Utterance.appliesTo .uniqueShapeWord .uniqueColor = false ∧
    Utterance.appliesTo .uniqueShapeWord .bothShared = false :=
  ⟨rfl, rfl, rfl⟩

/-- uniqueColorWord uniquely identifies uniqueColor. -/
theorem uniqueColorWord_unique :
    Utterance.appliesTo .uniqueColorWord .uniqueColor = true ∧
    Utterance.appliesTo .uniqueColorWord .uniqueShape = false ∧
    Utterance.appliesTo .uniqueColorWord .bothShared = false :=
  ⟨rfl, rfl, rfl⟩

/-- sharedShapeWord is ambiguous (applies to uniqueColor and bothShared). -/
theorem sharedShapeWord_ambiguous :
    Utterance.appliesTo .sharedShapeWord .uniqueColor = true ∧
    Utterance.appliesTo .sharedShapeWord .bothShared = true ∧
    Utterance.appliesTo .sharedShapeWord .uniqueShape = false :=
  ⟨rfl, rfl, rfl⟩

/-- sharedColorWord is ambiguous (applies to uniqueShape and bothShared). -/
theorem sharedColorWord_ambiguous :
    Utterance.appliesTo .sharedColorWord .uniqueShape = true ∧
    Utterance.appliesTo .sharedColorWord .bothShared = true ∧
    Utterance.appliesTo .sharedColorWord .uniqueColor = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Speaker Predictions
-- ============================================================================

/-- Speakers prefer the unique-feature word for uniqueShape targets.

Since uniqueShapeWord applies to 1 object while sharedColorWord applies to 2,
L0(uniqueShape | uniqueShapeWord) = 1 > L0(uniqueShape | sharedColorWord) = 1/2.
The rpow score rpow(1, α) > rpow(1/2, α) for any α > 0, so S1 prefers it. -/
theorem speaker_prefers_unique_shape (αS : ℝ) (hα : 0 < αS) :
    (σ_bU αS hα (adjCost 0)).S1 () .uniqueShape .uniqueShapeWord >
    (σ_bU αS hα (adjCost 0)).S1 () .uniqueShape .sharedColorWord := by
  sorry -- TODO: prove via rpow monotonicity + policy monotonicity

/-- Speakers prefer the unique-feature word for uniqueColor targets. -/
theorem speaker_prefers_unique_color (αS : ℝ) (hα : 0 < αS) :
    (σ_bU αS hα (adjCost 0)).S1 () .uniqueColor .uniqueColorWord >
    (σ_bU αS hα (adjCost 0)).S1 () .uniqueColor .sharedShapeWord := by
  sorry -- TODO: prove via rpow monotonicity + policy monotonicity

/-- For bothShared with zero cost and uniform L0, the two ambiguous
utterances get equal S1 probability, by context symmetry.

uniqueShape has 1 unique feature + 1 shared feature.
uniqueColor has 1 unique feature + 1 shared feature.
bothShared shares one feature with each. The symmetry means
sharedColorWord and sharedShapeWord are equally informative. -/
theorem bothShared_symmetric (αS : ℝ) (hα : 0 < αS) :
    (σ_bU αS hα (adjCost 0)).S1 () .bothShared .sharedColorWord =
    (σ_bU αS hα (adjCost 0)).S1 () .bothShared .sharedShapeWord := by
  sorry -- TODO: prove via L0 value equality

-- ============================================================================
-- Listener Predictions
-- ============================================================================

/-- Pragmatic inference for sharedColorWord ("green") with uniform prior.

L1 prefers bothShared (green circle) over uniqueShape (green square):
a speaker wanting uniqueShape would say uniqueShapeWord ("square")
since it uniquely identifies the target. Saying "green" signals the
speaker probably means the object without a unique feature. -/
theorem listener_green_pragmatic (αS : ℝ) (hα : 0 < αS) :
    (σ_bU αS hα (adjCost 0)).L1 .sharedColorWord .bothShared >
    (σ_bU αS hα (adjCost 0)).L1 .sharedColorWord .uniqueShape := by
  sorry -- TODO: prove via partition function comparison

/-- Pragmatic inference for sharedShapeWord ("circle") with salience prior.

With empirical salience, L1 may prefer uniqueColor (blue circle) over
bothShared (green circle), even though pragmatics alone would favor
bothShared. This is because uniqueColor is much more salient (139 vs 30
in the salience condition), overriding the pragmatic signal. -/
theorem listener_circle_with_salience (αS : ℝ) (hα : 0 < αS) :
    let cfg := mkConfig uniformPrior uniformPrior_nonneg
                 (beliefGoalScore (adjCost 0)) (beliefGoalScore_nonneg (adjCost 0))
                 empiricalSalience empiricalSalience_nonneg αS hα
    cfg.L1 .sharedShapeWord .uniqueColor >
    cfg.L1 .sharedShapeWord .bothShared := by
  sorry -- TODO: prove via salience-weighted score comparison

-- ============================================================================
-- Action-Oriented Listener Properties
-- ============================================================================

/-- The action-oriented listener produces a valid probability distribution. -/
theorem L1_action_pos (cfg : RSAConfig Utterance Object) (αL : ℝ)
    (u : Utterance) (w : Object) :
    0 < L1_action cfg αL u w := by
  exact softmax_pos _ _ _

theorem L1_action_sum_eq_one (cfg : RSAConfig Utterance Object) (αL : ℝ)
    (u : Utterance) :
    ∑ w : Object, L1_action cfg αL u w = 1 := by
  exact softmax_sum_eq_one _ _

/-- Higher L1 rationality (αL) sharpens the action-oriented listener's
distribution: if L1 prefers world w₁ over w₂ (L1(w₁|u) > L1(w₂|u)),
the action-oriented listener amplifies this preference. -/
theorem L1_action_amplifies (cfg : RSAConfig Utterance Object)
    {αL : ℝ} (hα : 0 < αL) (u : Utterance) (w₁ w₂ : Object)
    (h : cfg.L1 u w₁ > cfg.L1 u w₂) :
    L1_action cfg αL u w₁ > L1_action cfg αL u w₂ := by
  exact softmax_strict_mono _ hα _ _ h

/-
## Summary: What this file tests about the RSAConfig API

1. **Pluggable s1Score**: `beliefGoalScore` and `actionGoalScore` are different
   scoring functions, plugged into the same RSAConfig structure via `s1Score`.
   The API is agnostic to what the speaker optimizes.

2. **Meaning encodes speaker belief**: The speaker's assumption about L0
   (uniform vs salience-weighted) is captured by the `meaning` function.
   No separate "speaker belief" field is needed.

3. **Cost inside s1Score**: Utterance cost is part of the speaker's
   score function, not a separate RSAConfig field. This is clean because
   cost IS part of what the speaker optimizes.

4. **Independent listener prior**: `worldPrior` (the listener's prior at L1)
   is independent of `meaning` (which determines L0). This allows the
   speaker's belief about L0 and the listener's prior to vary independently,
   exactly as Q&F require.

5. **Composable extensions**: The action-oriented listener is defined as
   `softmax ∘ L1`, extending the API without modifying RSAConfig. The
   softmax properties (positivity, sum-to-one, monotonicity) transfer
   directly from Core.RationalAction.
-/

end RSA.QingFranke2013
