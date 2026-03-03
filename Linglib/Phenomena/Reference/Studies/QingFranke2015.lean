import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config

/-!
# @cite{qing-franke-2015}
@cite{frank-goodman-2012}

"Variations on a Bayesian Theme: Comparing Bayesian Models of Referential Reasoning"

## Paradigm

Three objects varying on two dimensions (color × shape) in a reference game:
{green_square, green_circle, blue_circle}. Speaker produces a single feature word;
listener identifies the target object.

Utterances: {square, circle, green, blue}

## The Decomposition

The paper decomposes Bayesian reference games along 3 orthogonal dimensions,
yielding a family of models that includes @cite{frank-goodman-2012} as one instance:

### Speaker Belief (y ∈ {U, S}): What does L0 assume?

- **Uniform (U)**: L0 treats all referents equally:
  U(t|m) = ⟦m⟧(t) / |⟦m⟧| (Eq. 1)
- **Salience (S)**: L0 weights by perceptual salience:
  S(t|m) = S(t) · ⟦m⟧(t) / Σ_t' S(t') · ⟦m⟧(t')

This enters the RSAConfig via `meaning`: uniform uses constant 1 for true worlds;
salience uses S(w) for true worlds.

### Speaker Goal (x ∈ {a, b}): What does the speaker optimize?

- **Belief-oriented (b)**: maximize log-probability of correct belief
  σ_b(m|t) ∝ exp(λ_S · (log y(t|m) - Cost(m))) (Eq. 10)
- **Action-oriented (a)**: maximize probability of correct action
  σ_a(m|t) ∝ exp(λ_S · (y(t|m) - Cost(m))) (Eq. 9)

This enters via `s1Score`: belief-oriented uses log L0; action-oriented uses raw L0.

### Listener Action: How does the listener choose?

- **Belief-oriented (b)**: standard Bayesian update
  ρ_b(t|m) ∝ v(t) · σ(m|t) (Eq. 15)
- **Action-oriented (a)**: softmax over Bayesian posterior
  ρ_a(t|m) ∝ exp(α_L · ρ_b(t|m)) (Eq. 14)

The belief-oriented listener IS `RSAConfig.L1`. The action-oriented listener is
a composable extension defined as `softmax ∘ L1`.

## Speaker Models (4 variants)

| Model | Goal | Belief | S1 Score |
|-------|------|--------|----------|
| σ_bU  | belief | uniform | exp(λ · (log U(t\|m) - C(m))) |
| σ_aU  | action | uniform | exp(λ · (U(t\|m) - C(m))) |
| σ_bS  | belief | salience | exp(λ · (log S(t\|m) - C(m))) |
| σ_aS  | action | salience | exp(λ · (S(t\|m) - C(m))) |

σ_bU is standard RSA with utterance costs.

## Key Findings

**Speaker data** (Table 1, N=144 per target): σ_bU and σ_aU best explain production
data (Table 3). Salience in the speaker does NOT help. Cost preference exists (c > 0).

**Listener data** (Table 2, N=180 per utterance): Salience-prior models dominate in
model comparison (Table 4). Best overall: ρ_aS(σ_aU) with informed-correlated
hyperprior.

**Salience reversal**: Uniform and salience priors make **opposite** L1 predictions
for ambiguous utterances. For "circle", human data matches the salience direction
(blue_circle: 117/180 = 65%). For "green", human data matches the pragmatic
direction (green_circle: 115/180 = 64%), NOT salience.

## Qualitative Findings

| # | Finding | Type | Config |
|---|---------|------|--------|
| 1 | `speaker_prefers_unique_shape` | S1: "square" > "green" for green_sq | σ_bU |
| 2 | `speaker_prefers_unique_color` | S1: "blue" > "circle" for blue_circ | σ_bU |
| 3 | `cost_breaks_symmetry` | S1: "circle" > "green" for green_circ | σ_bU |
| 4 | `no_cost_symmetry` | ¬(S1 "circle" > "green" for green_circ) | σ_bU, no cost |
| 5 | `salience_reversal_circle` | uniform vs salience L1 flip for "circle" | σ_bU |
| 6 | `salience_reversal_green` | uniform vs salience L1 flip for "green" | σ_bU |

-/

set_option autoImplicit false

namespace Phenomena.Reference.Studies.QingFranke2015

open Phenomena RSA BigOperators Core
open Real (exp log exp_pos exp_lt_exp)

-- ============================================================================
-- §1. Empirical Data
-- ============================================================================

/-- The 6 qualitative findings from @cite{qing-franke-2015}. -/
inductive Finding where
  /-- For green_square targets, speakers prefer the unique shape word "square"
      over the shared color word "green". Evidence: 135/144 trials (Table 1). -/
  | speaker_prefers_unique_shape
  /-- For blue_circle targets, speakers prefer the unique color word "blue"
      over the shared shape word "circle". Evidence: 119/144 trials (Table 1). -/
  | speaker_prefers_unique_color
  /-- For green_circle targets, cost breaks the symmetry between the two
      ambiguous words: S1 prefers "circle" (noun, cost=0) over "green"
      (adjective, cost=1/2). Evidence: 81/144 chose "circle" (Table 1). -/
  | cost_breaks_symmetry
  /-- Without cost, the two ambiguous words for green_circle are symmetric:
      neither dominates the other. -/
  | no_cost_symmetry
  /-- Salience reversal for "circle": uniform L1 predicts green_circ > blue_circ,
      but salience L1 predicts blue_circ > green_circ. Human data matches the
      salience direction: 117/180 chose blue_circle (Table 2). -/
  | salience_reversal_circle
  /-- Salience reversal for "green": uniform L1 predicts green_circ > green_sq,
      but salience L1 predicts green_sq > green_circ. Human data matches the
      *pragmatic* direction: 115/180 chose green_circle (Table 2). The model
      predictions are correct; human data here follows pragmatics, not salience. -/
  | salience_reversal_green
  deriving DecidableEq, BEq, Repr

def findings : List Finding :=
  [.speaker_prefers_unique_shape, .speaker_prefers_unique_color,
   .cost_breaks_symmetry, .no_cost_symmetry,
   .salience_reversal_circle, .salience_reversal_green]

-- ============================================================================
-- §2. Domain Types
-- ============================================================================

/-- The three objects in the reference game context (Table 1).

    green_square: unique shape, shared color
    blue_circle: unique color, shared shape
    green_circle: both features shared -/
inductive Object where
  | green_square | blue_circle | green_circle
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

instance : Nonempty Object := ⟨.green_square⟩

/-- The four single-word utterances (feature predicates). -/
inductive Utterance where
  | square | circle | green | blue
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

instance : Nonempty Utterance := ⟨.square⟩

/-- Boolean semantics: ⟦utterance⟧(object).

    - "square" applies to green_square only (unique shape)
    - "circle" applies to blue_circle and green_circle (shared shape)
    - "green" applies to green_square and green_circle (shared color)
    - "blue" applies to blue_circle only (unique color) -/
def Utterance.appliesTo : Utterance → Object → Bool
  | .square, .green_square => true
  | .circle, .blue_circle  => true
  | .circle, .green_circle => true
  | .green,  .green_square => true
  | .green,  .green_circle => true
  | .blue,   .blue_circle  => true
  | _, _ => false

-- ============================================================================
-- §3. Cost Structure
-- ============================================================================

/-- Adjective cost: shape words (nouns) cost 0, color words (adjectives) cost c.
    From @cite{qing-franke-2015} Eq. 11: Cost(m) = c if m is an adjective, 0 otherwise. -/
noncomputable def adjCost (c : ℝ) : Utterance → ℝ
  | .square | .circle => 0
  | .green  | .blue   => c

-- ============================================================================
-- §4. Salience Data
-- ============================================================================

/-- Salience data from Table 2, salience condition (N = 240).

    Blue circle (139) is most salient; green circle (30) least. -/
def saliencePrior : Object → ℝ
  | .green_square => 71
  | .blue_circle  => 139
  | .green_circle => 30

theorem saliencePrior_nonneg : ∀ w, 0 ≤ saliencePrior w := by
  intro w; cases w <;> simp [saliencePrior]

-- ============================================================================
-- §5. Speaker Goal Types (Goal Dimension)
-- ============================================================================

/-- Belief-oriented S1 score [Eq. 10]:
    σ_b(m|t) ∝ exp(λ · (log y(t|m) - Cost(m)))

    The speaker maximizes log-probability of correct belief at L0. Gated by
    if-then-else because `log 0 = 0` in Lean (unlike WebPPL where `log 0 = -∞`
    naturally zeros out false utterances). -/
noncomputable def beliefGoalScore (cost : Utterance → ℝ) :
    (Utterance → Object → ℝ) → ℝ → Unit → Object → Utterance → ℝ :=
  fun l0 α _ w u =>
    if l0 u w = 0 then 0
    else exp (α * (log (l0 u w) - cost u))

theorem beliefGoalScore_nonneg (cost : Utterance → ℝ) :
    ∀ (l0 : Utterance → Object → ℝ) (α : ℝ) (l : Unit) (w : Object) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ beliefGoalScore cost l0 α l w u := by
  intro _ _ _ _ _ _ _; simp only [beliefGoalScore]; split
  · exact le_refl 0
  · exact le_of_lt (exp_pos _)

/-- Action-oriented S1 score [Eq. 9]:
    σ_a(m|t) ∝ exp(λ · (y(t|m) - Cost(m)))

    The speaker maximizes the raw probability that the listener picks the correct
    referent, rather than log-probability. Unlike beliefGoalScore, this gives
    nonzero score even for false utterances (exp(-λ·C) > 0 when y=0).
    The paper notes (Footnote 7) that model comparison restricts to truthful
    predictions; here the model comparison theorems (§13) only compare
    utterances that are true of the target object, so no gating is needed. -/
noncomputable def actionGoalScore (cost : Utterance → ℝ) :
    (Utterance → Object → ℝ) → ℝ → Unit → Object → Utterance → ℝ :=
  fun l0 α _ w u => exp (α * (l0 u w - cost u))

theorem actionGoalScore_nonneg (cost : Utterance → ℝ) :
    ∀ (l0 : Utterance → Object → ℝ) (α : ℝ) (l : Unit) (w : Object) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ actionGoalScore cost l0 α l w u :=
  fun _ _ _ _ _ _ _ => le_of_lt (exp_pos _)

-- ============================================================================
-- §6. RSAConfig Constructor
-- ============================================================================

/-- Uniform prior: all objects equally weighted. -/
def uniformPrior : Object → ℝ := fun _ => 1

theorem uniformPrior_nonneg : ∀ w, 0 ≤ uniformPrior w :=
  fun _ => le_of_lt one_pos

/-- Parametric Q&F RSAConfig constructor.

    Decouples the three orthogonal dimensions:
    - `speakerPrior`: belief dimension — baked into `meaning` as L0's prior weight
      (uniform = 1 for all; salience = S(w))
    - `s1` + `s1_nn`: goal dimension — beliefGoalScore or actionGoalScore
    - `listenerPrior`: listener's world prior at L1 (independent of speaker's belief)

    The speaker's belief about L0 and the listener's prior vary independently —
    the speaker may assume uniform L0 while the listener uses salience, or vice versa.
    This decoupling is a key feature of the RSAConfig API. -/
@[reducible]
noncomputable def mkConfig
    (speakerPrior : Object → ℝ) (sp_nn : ∀ w, 0 ≤ speakerPrior w)
    (s1 : (Utterance → Object → ℝ) → ℝ → Unit → Object → Utterance → ℝ)
    (s1_nn : ∀ (l0 : Utterance → Object → ℝ) (α : ℝ) (l : Unit) (w : Object) (u : Utterance),
      (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ s1 l0 α l w u)
    (listenerPrior : Object → ℝ) (lp_nn : ∀ w, 0 ≤ listenerPrior w) :
    RSAConfig Utterance Object where
  meaning _ u w := if u.appliesTo w then speakerPrior w else 0
  meaning_nonneg _ _ w := by
    split
    · exact sp_nn w
    · exact le_refl 0
  s1Score := s1
  s1Score_nonneg := s1_nn
  worldPrior := listenerPrior
  worldPrior_nonneg := lp_nn
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by positivity

-- ============================================================================
-- §7. The 4 Speaker Models
-- ============================================================================

/-- σ_bU: Belief-oriented speaker, uniform L0.
    This IS standard RSA with utterance costs.
    S1 score = exp(λ · (log U(t|m) - Cost(m))). -/
@[reducible]
noncomputable def σ_bU (cost : Utterance → ℝ) (lp : Object → ℝ) (lp_nn : ∀ w, 0 ≤ lp w) :
    RSAConfig Utterance Object :=
  mkConfig uniformPrior uniformPrior_nonneg
    (beliefGoalScore cost) (beliefGoalScore_nonneg cost)
    lp lp_nn

/-- σ_aU: Action-oriented speaker, uniform L0.
    S1 score = exp(λ · (U(t|m) - Cost(m))). -/
@[reducible]
noncomputable def σ_aU (cost : Utterance → ℝ) (lp : Object → ℝ) (lp_nn : ∀ w, 0 ≤ lp w) :
    RSAConfig Utterance Object :=
  mkConfig uniformPrior uniformPrior_nonneg
    (actionGoalScore cost) (actionGoalScore_nonneg cost)
    lp lp_nn

/-- σ_bS: Belief-oriented speaker, salience-weighted L0.
    The speaker assumes L0 weights worlds by perceptual salience:
    L0(t|m) ∝ S(t) · ⟦m⟧(t). S1 score = exp(λ · (log S(t|m) - Cost(m))). -/
@[reducible]
noncomputable def σ_bS (cost : Utterance → ℝ) (lp : Object → ℝ) (lp_nn : ∀ w, 0 ≤ lp w) :
    RSAConfig Utterance Object :=
  mkConfig saliencePrior saliencePrior_nonneg
    (beliefGoalScore cost) (beliefGoalScore_nonneg cost)
    lp lp_nn

/-- σ_aS: Action-oriented speaker, salience-weighted L0.
    Same salience-weighted L0 as σ_bS, but S1 score = exp(λ · (S(t|m) - Cost(m))). -/
@[reducible]
noncomputable def σ_aS (cost : Utterance → ℝ) (lp : Object → ℝ) (lp_nn : ∀ w, 0 ≤ lp w) :
    RSAConfig Utterance Object :=
  mkConfig saliencePrior saliencePrior_nonneg
    (actionGoalScore cost) (actionGoalScore_nonneg cost)
    lp lp_nn

-- ============================================================================
-- §8. Concrete Configs for Findings
-- ============================================================================

/-- σ_bU with zero cost, uniform listener prior.
    Used for finding 4 (no cost → no symmetry breaking). -/
@[reducible]
noncomputable def zeroCostCfg : RSAConfig Utterance Object :=
  σ_bU (fun _ => 0) uniformPrior uniformPrior_nonneg

/-- σ_bU with adjective cost = 1/2, uniform listener prior.
    Standard RSA with cost asymmetry. Used for speaker predictions (findings 1–3)
    and the uniform half of salience reversal (findings 5–6). -/
@[reducible]
noncomputable def costCfg : RSAConfig Utterance Object :=
  σ_bU (adjCost (1/2)) uniformPrior uniformPrior_nonneg

/-- σ_bU with adjective cost = 1/2, salience-weighted listener prior.
    Shares the same S1 policy as costCfg (same speaker model σ_bU) but produces
    different L1 posteriors because L1's Bayesian inversion uses a salience-weighted
    world prior [Eq. 15 with v = S]. Used for findings 5–6 (salience half). -/
@[reducible]
noncomputable def salienceCfg : RSAConfig Utterance Object :=
  σ_bU (adjCost (1/2)) saliencePrior saliencePrior_nonneg

-- ============================================================================
-- §9. Action-Oriented Listener (Listener Dimension)
-- ============================================================================

/-- Action-oriented listener: ρ_a(t|m) ∝ exp(α_L · ρ_b(t|m)) [Eq. 14].

    Applies a second softmax to the belief-oriented L1 posterior. This models a
    listener who soft-maximizes over Bayesian beliefs rather than reporting beliefs
    directly. Provides an additional degree of freedom (α_L) for fitting listener
    data — the best overall model in the paper uses ρ_a.

    The RSAConfig API doesn't directly support this, so it's defined as a composable
    extension, demonstrating that the API is open for extension without modification. -/
noncomputable def L1_action {U W : Type*} [Fintype U] [Fintype W]
    (cfg : RSAConfig U W) (αL : ℝ) (u : U) (w : W) : ℝ :=
  softmax (cfg.L1 u) αL w

/-- The action-oriented listener always assigns positive probability. -/
theorem L1_action_pos {U W : Type*} [Fintype U] [Fintype W] [Nonempty W]
    (cfg : RSAConfig U W) (αL : ℝ) (u : U) (w : W) :
    0 < L1_action cfg αL u w :=
  softmax_pos _ _ _

/-- The action-oriented listener produces a valid probability distribution. -/
theorem L1_action_sum_eq_one {U W : Type*} [Fintype U] [Fintype W] [Nonempty W]
    (cfg : RSAConfig U W) (αL : ℝ) (u : U) :
    ∑ w : W, L1_action cfg αL u w = 1 :=
  softmax_sum_eq_one _ _

/-- Higher α_L sharpens the action-oriented listener's distribution:
    if L1 prefers w₁ over w₂, ρ_a amplifies this preference. -/
theorem L1_action_amplifies {U W : Type*} [Fintype U] [Fintype W] [Nonempty W]
    (cfg : RSAConfig U W) {αL : ℝ} (hα : 0 < αL) (u : U) (w₁ w₂ : W)
    (h : cfg.L1 u w₁ > cfg.L1 u w₂) :
    L1_action cfg αL u w₁ > L1_action cfg αL u w₂ :=
  softmax_strict_mono _ hα _ _ h

-- ============================================================================
-- §10. Structural Properties
-- ============================================================================

/-- "square" uniquely identifies green_square. -/
theorem square_unique :
    Utterance.appliesTo .square .green_square = true ∧
    Utterance.appliesTo .square .blue_circle = false ∧
    Utterance.appliesTo .square .green_circle = false :=
  ⟨rfl, rfl, rfl⟩

/-- "blue" uniquely identifies blue_circle. -/
theorem blue_unique :
    Utterance.appliesTo .blue .blue_circle = true ∧
    Utterance.appliesTo .blue .green_square = false ∧
    Utterance.appliesTo .blue .green_circle = false :=
  ⟨rfl, rfl, rfl⟩

/-- "circle" is ambiguous between blue_circle and green_circle. -/
theorem circle_ambiguous :
    Utterance.appliesTo .circle .blue_circle = true ∧
    Utterance.appliesTo .circle .green_circle = true ∧
    Utterance.appliesTo .circle .green_square = false :=
  ⟨rfl, rfl, rfl⟩

/-- "green" is ambiguous between green_square and green_circle. -/
theorem green_ambiguous :
    Utterance.appliesTo .green .green_square = true ∧
    Utterance.appliesTo .green .green_circle = true ∧
    Utterance.appliesTo .green .blue_circle = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §11. Speaker Predictions (Findings 1–4)
-- ============================================================================

/-- Finding 1: For green_square, S1 prefers "square" (unique, cost=0) over "green"
    (ambiguous, cost=1/2). Both informativity and cost favor "square".
    Evidence: 135/144 speakers chose "square" (Table 1). -/
theorem speaker_prefers_unique_shape :
    costCfg.S1 () .green_square .square > costCfg.S1 () .green_square .green := by
  rsa_predict

/-- Finding 2: For blue_circle, S1 prefers "blue" (unique, cost=1/2) over "circle"
    (ambiguous, cost=0). Informativity dominates cost.
    Evidence: 119/144 speakers chose "blue" (Table 1). -/
theorem speaker_prefers_unique_color :
    costCfg.S1 () .blue_circle .blue > costCfg.S1 () .blue_circle .circle := by
  rsa_predict

/-- Finding 3: For green_circle, cost breaks the tie between the two ambiguous
    words: S1 prefers "circle" (cost=0) over "green" (cost=1/2). Both are equally
    informative (each applies to 2 objects), so cost is the tiebreaker.
    Evidence: 81/144 chose "circle", 63/144 chose "green" (Table 1;
    not statistically significant: χ²=2.25, p=0.13). -/
theorem cost_breaks_symmetry :
    costCfg.S1 () .green_circle .circle > costCfg.S1 () .green_circle .green := by
  rsa_predict

/-- Finding 4: Without cost, the symmetry is unbroken — neither ambiguous word
    dominates for green_circle. Both "circle" and "green" apply to exactly 2 objects,
    so L0 assigns equal probability, and S1 assigns equal weight. -/
theorem no_cost_symmetry :
    ¬(zeroCostCfg.S1 () .green_circle .circle > zeroCostCfg.S1 () .green_circle .green) := by
  rsa_predict

-- ============================================================================
-- §12. Listener Predictions (Findings 5–6): Salience Reversal
-- ============================================================================

/-! The paper's central contribution: perceptual salience **reverses** L1 predictions.

Under uniform prior (costCfg), pragmatic reasoning dominates: the listener infers
that ambiguous words signal the object without a unique alternative. Under salience
prior (salienceCfg), salience overrides pragmatics: salient objects dominate even
though pragmatics would favor the other.

The listener prior v ∈ {U, S} enters at L1 via `worldPrior`, independent of the
speaker's belief y ∈ {U, S} which enters at L0 via `meaning`. Both costCfg and
salienceCfg use σ_bU (speaker belief = uniform), but differ in the listener's
prior — exactly the comparison the paper runs (Table 4 rows for ρ_bU vs ρ_bS). -/

-- Finding 5: Salience reversal for "circle"
-- Uniform: green_circle > blue_circle (pragmatic narrowing)
-- Salience: blue_circle > green_circle (salience override; matches human 66%)

/-- Uniform L1 for "circle": green_circle > blue_circle.
    Pragmatic reasoning: a speaker wanting blue_circle would say "blue" (unique),
    so saying "circle" signals green_circle. -/
theorem uniform_circle_green_circ :
    costCfg.L1 .circle .green_circle > costCfg.L1 .circle .blue_circle := by
  rsa_predict

/-- Salience L1 for "circle": blue_circle > green_circle.
    Salience (139 vs 30) overrides pragmatic narrowing. Matches human data
    (Table 2: 117/180 = 65% chose blue_circle). -/
theorem salience_circle_blue_circ :
    salienceCfg.L1 .circle .blue_circle > salienceCfg.L1 .circle .green_circle := by
  rsa_predict

/-- Finding 5: Salience reversal for "circle". Uniform and salience priors make
    opposite L1 predictions, and human data matches the salience direction. -/
theorem salience_reversal_circle :
    (costCfg.L1 .circle .green_circle > costCfg.L1 .circle .blue_circle) ∧
    (salienceCfg.L1 .circle .blue_circle > salienceCfg.L1 .circle .green_circle) :=
  ⟨uniform_circle_green_circ, salience_circle_blue_circ⟩

-- Finding 6: Salience reversal for "green"
-- Uniform: green_circle > green_square (pragmatic narrowing)
-- Salience: green_square > green_circle (salience override; matches human 56%)

/-- Uniform L1 for "green": green_circle > green_square.
    Pragmatic reasoning: a speaker wanting green_square would say "square" (unique),
    so saying "green" signals green_circle. -/
theorem uniform_green_green_circ :
    costCfg.L1 .green .green_circle > costCfg.L1 .green .green_square := by
  rsa_predict

/-- Salience L1 for "green": green_square > green_circle.
    Salience (71 vs 30) overrides pragmatic narrowing in the model. However,
    human data goes in the opposite (pragmatic) direction: Table 2 shows
    115/180 = 64% chose green_circle. -/
theorem salience_green_green_sq :
    salienceCfg.L1 .green .green_square > salienceCfg.L1 .green .green_circle := by
  rsa_predict

/-- Finding 6: Salience reversal for "green". Uniform and salience priors make
    opposite L1 predictions. Human data matches the *pragmatic* (uniform)
    direction: 115/180 chose green_circle (Table 2). -/
theorem salience_reversal_green :
    (costCfg.L1 .green .green_circle > costCfg.L1 .green .green_square) ∧
    (salienceCfg.L1 .green .green_square > salienceCfg.L1 .green .green_circle) :=
  ⟨uniform_green_green_circ, salience_green_green_sq⟩

-- ============================================================================
-- §13. Model Comparison: Alternative Speaker Models
-- ============================================================================

/-! The paper compares 4 speaker models along the speaker-goal × speaker-belief
dimensions (Table 3). Only σ_bU correctly predicts all three speaker preferences.
Each alternative fails on at least one observation:

| Model | green_sq (sq > gr) | blue_circ (bl > ci) | green_circ (ci > gr) | Score |
|-------|-------------------|--------------------|--------------------|-------|
| σ_bU  | ✓                 | ✓                  | ✓                  | 3/3   |
| σ_aU  | ✓                 | = (tie)            | ✓                  | 2/3   |
| σ_bS  | ✓                 | ✗ (ci > bl)        | ✗ (gr > ci)        | 1/3   |
| σ_aS  | ✓                 | ✗ (ci > bl)        | ✓                  | 2/3   |

The discriminating observation is **blue_circle**: only σ_bU predicts "blue" > "circle".
σ_aU ties (equal S1 scores), while σ_bS and σ_aS reverse the preference.

Salience in the speaker is harmful: it inflates L0's posterior for blue_circle given
"circle" (since blue_circle has the highest salience, 139 vs 30), which raises S1's
score for "circle" enough to match or exceed "blue". -/

-- Concrete configs: all use adjCost 1/2 and uniform listener prior.
-- (Listener prior doesn't affect S1, so any prior works for speaker comparison.)

/-- σ_aU with adjective cost = 1/2. Action-oriented speaker, uniform L0.
    S1 score = exp(λ · (U(t|m) - Cost(m))). No exp/log cancellation. -/
@[reducible]
noncomputable def σ_aU_cfg : RSAConfig Utterance Object :=
  σ_aU (adjCost (1/2)) uniformPrior uniformPrior_nonneg

/-- σ_bS with adjective cost = 1/2. Belief-oriented speaker, salience-weighted L0.
    L0 weights worlds by perceptual salience; S1 score = exp(λ · (log S(t|m) - Cost(m))). -/
@[reducible]
noncomputable def σ_bS_cfg : RSAConfig Utterance Object :=
  σ_bS (adjCost (1/2)) uniformPrior uniformPrior_nonneg

/-- σ_aS with adjective cost = 1/2. Action-oriented speaker, salience-weighted L0. -/
@[reducible]
noncomputable def σ_aS_cfg : RSAConfig Utterance Object :=
  σ_aS (adjCost (1/2)) uniformPrior uniformPrior_nonneg

-- §13a. σ_aU: Action-oriented, uniform belief
-- Agrees on green_sq and green_circ; ties on blue_circ.
-- The tie arises because exp/log don't cancel in actionGoalScore:
-- score(blue) = exp(1 * (1 - 1/2)) = exp(1/2)
-- score(circle) = exp(1 * (1/2 - 0)) = exp(1/2)

/-- σ_aU agrees: "square" > "green" for green_square. -/
theorem σ_aU_green_sq :
    σ_aU_cfg.S1 () .green_square .square > σ_aU_cfg.S1 () .green_square .green := by
  rsa_predict

/-- σ_aU agrees: "circle" > "green" for green_circle (cost breaks symmetry). -/
theorem σ_aU_green_circ :
    σ_aU_cfg.S1 () .green_circle .circle > σ_aU_cfg.S1 () .green_circle .green := by
  rsa_predict

/-- σ_aU fails: "blue" and "circle" are tied for blue_circle.
    This is the key prediction that distinguishes σ_aU from σ_bU.
    Under belief-oriented scoring (σ_bU), the log transform amplifies the
    informativity advantage of "blue" (L0 = 1) over "circle" (L0 = 1/2);
    under action-oriented scoring (σ_aU), the raw difference is exactly
    offset by cost. -/
theorem σ_aU_blue_circ_tie :
    ¬(σ_aU_cfg.S1 () .blue_circle .blue > σ_aU_cfg.S1 () .blue_circle .circle) ∧
    ¬(σ_aU_cfg.S1 () .blue_circle .circle > σ_aU_cfg.S1 () .blue_circle .blue) :=
  ⟨by rsa_predict, by rsa_predict⟩

-- §13b. σ_bS: Belief-oriented, salience belief
-- Agrees on green_sq; reverses on both blue_circ and green_circ.
-- Worst speaker model (1/3).

/-- σ_bS agrees: "square" > "green" for green_square.
    The unique shape word wins regardless of speaker belief, since "square"
    applies to only one object while "green" is ambiguous. -/
theorem σ_bS_green_sq :
    σ_bS_cfg.S1 () .green_square .square > σ_bS_cfg.S1 () .green_square .green := by
  rsa_predict

/-- σ_bS reverses blue_circle: predicts "circle" > "blue".
    With salience-weighted L0, blue_circle has the highest salience (139),
    so L0(blue_circ|"circle") = 139/169 ≈ 0.82, making "circle" quite
    informative. Combined with zero cost for "circle" vs cost 1/2 for "blue",
    the pragmatic advantage of "blue" is overcome. -/
theorem σ_bS_blue_circ_reversal :
    σ_bS_cfg.S1 () .blue_circle .circle > σ_bS_cfg.S1 () .blue_circle .blue := by
  rsa_predict

/-- σ_bS reverses green_circle: predicts "green" > "circle".
    With salience weights, L0(green_circ|"green") = 30/101 ≈ 0.30 and
    L0(green_circ|"circle") = 30/169 ≈ 0.18. "green" has higher L0 posterior
    for green_circ, and the log transform in belief-oriented scoring
    amplifies this advantage enough to overcome its cost disadvantage. -/
theorem σ_bS_green_circ_reversal :
    σ_bS_cfg.S1 () .green_circle .green > σ_bS_cfg.S1 () .green_circle .circle := by
  rsa_predict

-- §13c. σ_aS: Action-oriented, salience belief
-- Agrees on green_sq and green_circ; reverses on blue_circ.

/-- σ_aS agrees: "square" > "green" for green_square. -/
theorem σ_aS_green_sq :
    σ_aS_cfg.S1 () .green_square .square > σ_aS_cfg.S1 () .green_square .green := by
  rsa_predict

/-- σ_aS reverses blue_circle: predicts "circle" > "blue".
    Same mechanism as σ_bS: salience inflates L0(blue_circ|"circle") = 139/169.
    Under action-oriented scoring, this raw probability advantage
    (plus zero cost) overcomes "blue"'s informativity. -/
theorem σ_aS_blue_circ_reversal :
    σ_aS_cfg.S1 () .blue_circle .circle > σ_aS_cfg.S1 () .blue_circle .blue := by
  rsa_predict

/-- σ_aS agrees: "circle" > "green" for green_circle.
    Unlike σ_bS, the action-oriented scoring doesn't amplify the L0
    advantage of "green" via log, so cost wins for green_circle. -/
theorem σ_aS_green_circ :
    σ_aS_cfg.S1 () .green_circle .circle > σ_aS_cfg.S1 () .green_circle .green := by
  rsa_predict

-- §13d. Capstone: σ_bU is the best speaker model

/-- σ_bU uniquely predicts "blue" > "circle" for blue_circle.

    The blue_circle observation is the decisive test: 119/144 speakers chose "blue"
    over "circle" (Table 1). σ_bU is the only model that predicts this:
    - σ_bU: blue > circle (correct) — log transform amplifies informativity
    - σ_aU: blue = circle (tie) — raw probability and cost exactly cancel
    - σ_bS: circle > blue (reversal) — salience makes "circle" informative
    - σ_aS: circle > blue (reversal) — same salience effect

    This is Q&F's main speaker-side finding: standard RSA (belief-oriented,
    uniform L0) best explains production data. -/
theorem σ_bU_best_speaker_model :
    -- σ_bU correctly predicts blue > circle
    (costCfg.S1 () .blue_circle .blue > costCfg.S1 () .blue_circle .circle) ∧
    -- σ_aU ties: neither blue > circle nor circle > blue
    (¬(σ_aU_cfg.S1 () .blue_circle .blue > σ_aU_cfg.S1 () .blue_circle .circle) ∧
     ¬(σ_aU_cfg.S1 () .blue_circle .circle > σ_aU_cfg.S1 () .blue_circle .blue)) ∧
    -- σ_bS reverses: circle > blue
    (σ_bS_cfg.S1 () .blue_circle .circle > σ_bS_cfg.S1 () .blue_circle .blue) ∧
    -- σ_aS reverses: circle > blue
    (σ_aS_cfg.S1 () .blue_circle .circle > σ_aS_cfg.S1 () .blue_circle .blue) :=
  ⟨speaker_prefers_unique_color, σ_aU_blue_circ_tie,
   σ_bS_blue_circ_reversal, σ_aS_blue_circ_reversal⟩

-- ============================================================================
-- §14. Verification
-- ============================================================================

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .speaker_prefers_unique_shape =>
      costCfg.S1 () .green_square .square > costCfg.S1 () .green_square .green
  | .speaker_prefers_unique_color =>
      costCfg.S1 () .blue_circle .blue > costCfg.S1 () .blue_circle .circle
  | .cost_breaks_symmetry =>
      costCfg.S1 () .green_circle .circle > costCfg.S1 () .green_circle .green
  | .no_cost_symmetry =>
      ¬(zeroCostCfg.S1 () .green_circle .circle > zeroCostCfg.S1 () .green_circle .green)
  | .salience_reversal_circle =>
      (costCfg.L1 .circle .green_circle > costCfg.L1 .circle .blue_circle) ∧
      (salienceCfg.L1 .circle .blue_circle > salienceCfg.L1 .circle .green_circle)
  | .salience_reversal_green =>
      (costCfg.L1 .green .green_circle > costCfg.L1 .green .green_square) ∧
      (salienceCfg.L1 .green .green_square > salienceCfg.L1 .green .green_circle)

/-- The RSA model accounts for all 6 qualitative findings from @cite{qing-franke-2015}. -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact speaker_prefers_unique_shape
  · exact speaker_prefers_unique_color
  · exact cost_breaks_symmetry
  · exact no_cost_symmetry
  · exact salience_reversal_circle
  · exact salience_reversal_green

-- ============================================================================
-- §15. λ-Independence of Speaker Rankings
-- ============================================================================

/-! The speaker ranking under both belief-oriented and action-oriented scoring
is **completely independent of λ** (the rationality parameter). Since `exp`
is strictly monotone and multiplication by λ > 0 preserves strict order:

    exp(λ · a) > exp(λ · b) ⟺ a > b (for λ > 0)

**Consequence**: The qualitative predictions (findings 1–4) hold for ALL λ > 0.
The paper's strong rejection of λ = 1 (§5) affects only the *magnitude* of
preferences (softmax temperature), not their *direction*. The existing
`rsa_predict` proofs at α = 1 establish log(L0) − cost orderings that hold
at every positive α.

Cost thresholds (the exact c ranges where each finding holds):
- **Finding 1** (sq > gr for green_sq): all c ≥ 0 (log 1 − 0 > log ½ − c)
- **Finding 2** (bl > ci for blue_circ): c < ln 2 ≈ 0.693 (see §16)
- **Finding 3** (ci > gr for green_circ): all c > 0 (log ½ − 0 > log ½ − c)
- **Finding 4** (ci = gr, no cost): equality, independent of everything -/

/-- Belief-oriented score ranking reduces to log L0 minus cost, independent of λ.

    For two truthful utterances (l0 ≠ 0 for both), the beliefGoalScore comparison
    is equivalent to comparing `log L0 − cost`, which has no λ dependence.
    Combined with `RationalAction.policy_gt_of_score_gt`, this means all
    qualitative belief-oriented S1 predictions are λ-independent. -/
theorem beliefGoal_gt_iff
    (cost : Utterance → ℝ) (l0 : Utterance → Object → ℝ)
    (u₁ u₂ : Utterance) (w : Object)
    {α : ℝ} (hα : 0 < α)
    (h1 : l0 u₁ w ≠ 0) (h2 : l0 u₂ w ≠ 0) :
    beliefGoalScore cost l0 α () w u₁ > beliefGoalScore cost l0 α () w u₂ ↔
    log (l0 u₁ w) - cost u₁ > log (l0 u₂ w) - cost u₂ := by
  simp only [beliefGoalScore, if_neg h1, if_neg h2]
  exact ⟨fun h => lt_of_mul_lt_mul_left (exp_lt_exp.mp h) (le_of_lt hα),
         fun h => exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hα)⟩

/-- Action-oriented score ranking reduces to L0 minus cost, independent of λ.

    Same λ-independence as belief-oriented, but comparing raw L0 rather than
    log L0. The difference between σ_a and σ_b is not λ-sensitivity (both are
    λ-independent) but how they *transform* L0: log compresses the informativity
    scale, amplifying small differences in L0 posterior. -/
theorem actionGoal_gt_iff
    (cost : Utterance → ℝ) (l0 : Utterance → Object → ℝ)
    (u₁ u₂ : Utterance) (w : Object)
    {α : ℝ} (hα : 0 < α) :
    actionGoalScore cost l0 α () w u₁ > actionGoalScore cost l0 α () w u₂ ↔
    l0 u₁ w - cost u₁ > l0 u₂ w - cost u₂ := by
  simp only [actionGoalScore]
  exact ⟨fun h => lt_of_mul_lt_mul_left (exp_lt_exp.mp h) (le_of_lt hα),
         fun h => exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hα)⟩

-- ============================================================================
-- §16. Cost Thresholds
-- ============================================================================

/-! The σ_aU tie at c = 1/2 (§13a) is the **exact boundary**: σ_aU predicts
"blue" > "circle" for blue_circle iff c < 1/2. Action-oriented scoring uses
raw L0: 1 − c > 1/2 − 0 ⟺ c < 1/2.

Belief-oriented scoring (σ_bU) uses log L0, giving a wider threshold of
c < ln 2 ≈ 0.693: log 1 − c > log(1/2) − 0 ⟺ c < ln 2.

Figure 4 shows that the posterior over c for σ_bU peaks around c ≈ 0.15,
well below the ln 2 ≈ 0.693 threshold. So the MAP cost estimate is
consistent with σ_bU correctly predicting blue > circle. -/

/-- σ_aU cost threshold for blue_circle: "blue" > "circle" ⟺ c < 1/2.

    Given L0(blue_circ|"blue") = 1 and L0(blue_circ|"circle") = 1/2,
    the action-oriented comparison reduces to 1 − c > 1/2. The existing tie
    `σ_aU_blue_circ_tie` is the corollary at c = 1/2. -/
theorem σ_aU_blue_circ_threshold
    {l0 : Utterance → Object → ℝ} {c : ℝ} {α : ℝ} (hα : 0 < α)
    (hbl : l0 .blue .blue_circle = 1) (hci : l0 .circle .blue_circle = 1/2) :
    actionGoalScore (adjCost c) l0 α () .blue_circle .blue >
    actionGoalScore (adjCost c) l0 α () .blue_circle .circle ↔ c < 1/2 := by
  rw [actionGoal_gt_iff _ _ _ _ _ hα]
  simp only [hbl, hci, adjCost]
  constructor <;> intro h <;> linarith

/-- σ_bU cost threshold for blue_circle: "blue" > "circle" ⟺ c < ln 2.

    Belief-oriented scoring uses log, so the threshold is wider than σ_aU's
    (ln 2 ≈ 0.693 > 0.5). This explains why σ_bU accommodates cost better
    than σ_aU: the log transform amplifies informativity differences,
    leaving more room for cost before the ranking flips. -/
theorem σ_bU_blue_circ_threshold
    {l0 : Utterance → Object → ℝ} {c : ℝ} {α : ℝ} (hα : 0 < α)
    (hbl : l0 .blue .blue_circle = 1) (hci : l0 .circle .blue_circle = 1/2)
    (hbl_ne : l0 .blue .blue_circle ≠ 0) (hci_ne : l0 .circle .blue_circle ≠ 0) :
    beliefGoalScore (adjCost c) l0 α () .blue_circle .blue >
    beliefGoalScore (adjCost c) l0 α () .blue_circle .circle ↔ c < log 2 := by
  rw [beliefGoal_gt_iff _ _ _ _ _ hα hbl_ne hci_ne]
  simp only [hbl, hci, adjCost, Real.log_one]
  have hlog : log ((1:ℝ) / 2) = -log 2 := by rw [one_div, Real.log_inv]
  rw [hlog]
  constructor <;> intro h <;> linarith

-- ============================================================================
-- §17. Raw Experimental Data (Tables 1–2)
-- ============================================================================

/-! Production and comprehension counts from the experiment (N = 1032 total:
432 speakers, 600 listeners). These connect model predictions to empirical
observations. -/

/-- Speaker production data from Table 1 (N = 144 per target object).

    - green_square: 135 "square", 9 "green" (93.8% unique shape)
    - blue_circle: 119 "blue", 25 "circle" (82.6% unique color)
    - green_circle: 81 "circle", 63 "green" (56.3% preferred noun; n.s.) -/
def speakerData : Object → Utterance → Nat
  | .green_square, .square => 135
  | .green_square, .green  => 9
  | .blue_circle,  .blue   => 119
  | .blue_circle,  .circle => 25
  | .green_circle, .circle => 81
  | .green_circle, .green  => 63
  | _, _                    => 0

/-- Listener comprehension data from Table 2 (N = 180 per ambiguous utterance).

    - "circle": 117 blue_circle, 62 green_circle, 1 green_square (65% salience)
    - "green": 65 green_square, 115 green_circle (64% pragmatic direction) -/
def listenerData : Utterance → Object → Nat
  | .circle, .blue_circle  => 117
  | .circle, .green_circle => 62
  | .circle, .green_square => 1
  | .green,  .green_square => 65
  | .green,  .green_circle => 115
  | _, _                    => 0

/-- Speaker data sums to N = 144 per target. -/
theorem speakerData_consistent :
    speakerData .green_square .square + speakerData .green_square .green = 144 ∧
    speakerData .blue_circle .blue + speakerData .blue_circle .circle = 144 ∧
    speakerData .green_circle .circle + speakerData .green_circle .green = 144 :=
  ⟨rfl, rfl, rfl⟩

/-- Listener data sums to N = 180 per ambiguous utterance. -/
theorem listenerData_consistent :
    listenerData .circle .blue_circle + listenerData .circle .green_circle
      + listenerData .circle .green_square = 180 ∧
    listenerData .green .green_square + listenerData .green .green_circle = 180 :=
  ⟨rfl, rfl⟩

/-- Speaker majority choice agrees with σ_bU S1 ranking (findings 1–3). -/
theorem speakerData_matches_model :
    speakerData .green_square .square > speakerData .green_square .green ∧
    speakerData .blue_circle .blue > speakerData .blue_circle .circle ∧
    speakerData .green_circle .circle > speakerData .green_circle .green :=
  ⟨by decide, by decide, by decide⟩

/-- For "circle", listener majority matches the salience L1 direction (finding 5):
    blue_circle (117) > green_circle (62). -/
theorem listenerData_circle_matches_salience :
    listenerData .circle .blue_circle > listenerData .circle .green_circle :=
  by decide

/-- For "green", listener majority matches the pragmatic/uniform L1 direction,
    NOT the salience direction: green_circle (115) > green_square (65).
    The paper notes this explicitly (p. 212). -/
theorem listenerData_green_matches_pragmatic :
    listenerData .green .green_circle > listenerData .green .green_square :=
  by decide

-- ============================================================================
-- §18. FG2012 Bridge
-- ============================================================================

/-! σ_bU with zero cost IS @cite{frank-goodman-2012}'s model. FG2012 defines:

    s1Score l0 α _ w u := if l0 u w = 0 then 0 else exp(α * log(l0 u w))

which equals `beliefGoalScore (fun _ => 0)` since `x − 0 = x` (`sub_zero`).

FG2012 uses multiple reference game contexts across 7 conditions; Q&F's
experiment (§4) focuses on one configuration: {green_square, green_circle,
blue_circle}. The scoring rule, compositional pattern, and RSAConfig structure
are identical — Q&F's contribution is decomposing along the cost, goal, and
salience dimensions. -/

/-- Zero-cost belief-oriented scoring equals FG2012's scoring rule.

    `beliefGoalScore (fun _ => 0)` reduces to `if l0 = 0 then 0 else exp(α * log l0)`
    by `sub_zero`. This is the formal statement that σ_bU generalizes FG2012
    by adding utterance cost — setting cost to zero recovers the original model. -/
theorem zeroCost_beliefGoal_eq
    (l0 : Utterance → Object → ℝ) (α : ℝ) (w : Object) (u : Utterance) :
    beliefGoalScore (fun _ => (0 : ℝ)) l0 α () w u =
    if l0 u w = 0 then 0 else exp (α * log (l0 u w)) := by
  simp [beliefGoalScore, sub_zero]

/-!
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

6. **Model comparison**: All 4 speaker models instantiate the same RSAConfig
   API with different `s1Score` and `meaning` choices. `rsa_predict` handles
   all comparisons including score-equality ties (σ_aU, zeroCost). The
   capstone theorem shows σ_bU uniquely predicts the blue_circle observation.

7. **λ-independence** (§15): `beliefGoal_gt_iff` and `actionGoal_gt_iff` prove
   that speaker rankings depend only on `log L0 − cost` (or `L0 − cost`),
   not on the rationality parameter λ. The paper's rejection of λ = 1 affects
   only quantitative fit, not qualitative predictions.

8. **Cost thresholds** (§16): `σ_aU_blue_circ_threshold` (c < 1/2) and
   `σ_bU_blue_circ_threshold` (c < ln 2) give the exact cost boundaries
   for each model's blue_circle prediction. The log transform in σ_bU
   widens the viable cost range.

9. **Raw data** (§17): `speakerData` and `listenerData` formalize Tables 1–2.
   `speakerData_matches_model` verifies that speaker majority choices match
   σ_bU predictions. `listenerData_circle_matches_salience` confirms "circle"
   follows salience; `listenerData_green_matches_pragmatic` confirms "green"
   follows pragmatics — a richer pattern than uniform salience dominance.

10. **FG2012 bridge** (§18): `zeroCost_beliefGoal_eq` proves that belief-oriented
    scoring at zero cost recovers @cite{frank-goodman-2012}'s scoring rule.
-/

end Phenomena.Reference.Studies.QingFranke2015
