import Linglib.Core.Empirical
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config

/-!
# Qing & Franke (2015) @cite{qing-franke-2015}

"Variations on a Bayesian Theme: Comparing Bayesian Models of Referential Reasoning"

## Paradigm

Three objects varying on two dimensions (color × shape) in a reference game:
{green_square, green_circle, blue_circle}. Speaker produces a single feature word;
listener identifies the target object.

Utterances: {square, circle, green, blue}

## The Decomposition

The paper decomposes Bayesian reference games along 3 orthogonal dimensions,
yielding a family of models that includes Frank & Goodman (2012) as one instance:

### Speaker Belief (y ∈ {U, S}): What does L0 assume?

- **Uniform (U)**: L0 treats all referents equally:
  U(t|m) = ⟦m⟧(t) / |⟦m⟧|                              [Eq. 1]
- **Salience (S)**: L0 weights by perceptual salience:
  S(t|m) = S(t) · ⟦m⟧(t) / Σ_t' S(t') · ⟦m⟧(t')       [Eq. 2]

This enters the RSAConfig via `meaning`: uniform uses constant 1 for true worlds;
salience uses S(w) for true worlds.

### Speaker Goal (x ∈ {a, b}): What does the speaker optimize?

- **Belief-oriented (b)**: maximize log-probability of correct belief
  σ_b(m|t) ∝ exp(λ_S · (log y(t|m) - Cost(m)))          [Eq. 10]
- **Action-oriented (a)**: maximize probability of correct action
  σ_a(m|t) ∝ exp(λ_S · (y(t|m) - Cost(m)))              [Eq. 9]

This enters via `s1Score`: belief-oriented uses log L0; action-oriented uses raw L0.

### Listener Action: How does the listener choose?

- **Belief-oriented (b)**: standard Bayesian update
  ρ_b(t|m) ∝ v(t) · σ(m|t)                              [Eq. 13/15]
- **Action-oriented (a)**: softmax over Bayesian posterior
  ρ_a(t|m) ∝ exp(α_L · ρ_b(t|m))                        [Eq. 14]

The belief-oriented listener IS `RSAConfig.L1`. The action-oriented listener is
a composable extension defined as `softmax ∘ L1`.

## Speaker Models (4 variants)

| Model | Goal | Belief | S1 Score |
|-------|------|--------|----------|
| σ_bU  | belief | uniform | exp(λ · (log U(t\|m) - C(m))) |
| σ_aU  | action | uniform | exp(λ · (U(t\|m) - C(m))) |
| σ_bS  | belief | salience | exp(λ · (log S(t\|m) - C(m))) |
| σ_aS  | action | salience | exp(λ · (S(t\|m) - C(m))) |

σ_bU is standard RSA (Frank & Goodman 2012) with utterance costs.

## Key Findings

**Speaker data** (Table 3): σ_bU and σ_aU best explain production data.
Salience in the speaker does NOT help. Cost preference exists (c > 0).

**Listener data** (Table 4): Salience-prior models dominate. The action-oriented
listener ρ_a provides additional flexibility. Best overall: ρ_aS(σ_aU).

**Salience reversal**: Uniform and salience priors make **opposite** L1 predictions
for ambiguous utterances. Human listener data matches the salience direction.

## Qualitative Findings

| # | Finding | Type | Config |
|---|---------|------|--------|
| 1 | `speaker_prefers_unique_shape` | S1: "square" > "green" for green_sq | σ_bU |
| 2 | `speaker_prefers_unique_color` | S1: "blue" > "circle" for blue_circ | σ_bU |
| 3 | `cost_breaks_symmetry` | S1: "circle" > "green" for green_circ | σ_bU |
| 4 | `no_cost_symmetry` | ¬(S1 "circle" > "green" for green_circ) | σ_bU, no cost |
| 5 | `salience_reversal_circle` | uniform vs salience L1 flip for "circle" | σ_bU |
| 6 | `salience_reversal_green` | uniform vs salience L1 flip for "green" | σ_bU |

## References

- Qing, C. & Franke, M. (2015). Variations on a Bayesian Theme: Comparing Bayesian
  Models of Referential Reasoning. In H. Zeevat & H.-C. Schmitz (Eds.), *Bayesian
  Natural Language Semantics and Pragmatics*, pp. 201–220. Springer.
- Frank, M.C. & Goodman, N.D. (2012). Predicting Pragmatic Reasoning in Language Games.
-/

set_option autoImplicit false

namespace Phenomena.Reference.Studies.QingFranke2015

open Phenomena RSA BigOperators Core
open Real (exp log exp_pos)

-- ============================================================================
-- §1. Empirical Data
-- ============================================================================

def citation : String :=
  "Qing & Franke (2015). In Bayesian Natural Language Semantics and Pragmatics, pp. 201-220."

def measure : MeasureSpec :=
  { scale := .proportion, task := .forcedChoice, unit := "proportion" }

/-- The 6 qualitative findings from Qing & Franke (2015). -/
inductive Finding where
  /-- For green_square targets, speakers prefer the unique shape word "square"
      over the shared color word "green". Evidence: 40/42 trials. -/
  | speaker_prefers_unique_shape
  /-- For blue_circle targets, speakers prefer the unique color word "blue"
      over the shared shape word "circle". Evidence: 36/42 trials. -/
  | speaker_prefers_unique_color
  /-- For green_circle targets, cost breaks the symmetry between the two
      ambiguous words: S1 prefers "circle" (noun, cost=0) over "green"
      (adjective, cost=1/2). Evidence: 30/42 chose "circle". -/
  | cost_breaks_symmetry
  /-- Without cost, the two ambiguous words for green_circle are symmetric:
      neither dominates the other. -/
  | no_cost_symmetry
  /-- Salience reversal for "circle": uniform L1 predicts green_circ > blue_circ,
      but salience L1 predicts blue_circ > green_circ (matching human data: 66%).
      This is the paper's central finding. -/
  | salience_reversal_circle
  /-- Salience reversal for "green": uniform L1 predicts green_circ > green_sq,
      but salience L1 predicts green_sq > green_circ (matching human data: 56%). -/
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
    From Q&F Eq. (11): Cost(m) = c if m is an adjective, 0 otherwise. -/
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
    This IS standard RSA (Frank & Goodman 2012) with utterance costs.
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

/-- Action-oriented listener: ρ_a(t|m) ∝ exp(α_L · ρ_b(t|m))  [Eq. 14].

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

set_option maxHeartbeats 400000 in
/-- Finding 1: For green_square, S1 prefers "square" (unique, cost=0) over "green"
    (ambiguous, cost=1/2). Both informativity and cost favor "square".
    Evidence: 40/42 speakers chose "square" (Table 3). -/
theorem speaker_prefers_unique_shape :
    costCfg.S1 () .green_square .square > costCfg.S1 () .green_square .green := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Finding 2: For blue_circle, S1 prefers "blue" (unique, cost=1/2) over "circle"
    (ambiguous, cost=0). Informativity dominates cost.
    Evidence: 36/42 speakers chose "blue" (Table 3). -/
theorem speaker_prefers_unique_color :
    costCfg.S1 () .blue_circle .blue > costCfg.S1 () .blue_circle .circle := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Finding 3: For green_circle, cost breaks the tie between the two ambiguous
    words: S1 prefers "circle" (cost=0) over "green" (cost=1/2). Both are equally
    informative (each applies to 2 objects), so cost is the tiebreaker.
    Evidence: 30/42 chose "circle", 12/42 chose "green" (Table 3). -/
theorem cost_breaks_symmetry :
    costCfg.S1 () .green_circle .circle > costCfg.S1 () .green_circle .green := by
  rsa_predict

set_option maxHeartbeats 400000 in
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

set_option maxHeartbeats 400000 in
/-- Uniform L1 for "circle": green_circle > blue_circle.
    Pragmatic reasoning: a speaker wanting blue_circle would say "blue" (unique),
    so saying "circle" signals green_circle. -/
theorem uniform_circle_green_circ :
    costCfg.L1 .circle .green_circle > costCfg.L1 .circle .blue_circle := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Salience L1 for "circle": blue_circle > green_circle.
    Salience (139 vs 30) overrides pragmatic narrowing. Matches human data (66%). -/
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

set_option maxHeartbeats 400000 in
/-- Uniform L1 for "green": green_circle > green_square.
    Pragmatic reasoning: a speaker wanting green_square would say "square" (unique),
    so saying "green" signals green_circle. -/
theorem uniform_green_green_circ :
    costCfg.L1 .green .green_circle > costCfg.L1 .green .green_square := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Salience L1 for "green": green_square > green_circle.
    Salience (71 vs 30) overrides pragmatic narrowing. Matches human data (56%). -/
theorem salience_green_green_sq :
    salienceCfg.L1 .green .green_square > salienceCfg.L1 .green .green_circle := by
  rsa_predict

/-- Finding 6: Salience reversal for "green". Uniform and salience priors make
    opposite L1 predictions, and human data matches the salience direction. -/
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

-- Auxiliary: expand finite sums for manual score-equality proofs

@[simp] private theorem Object.sum_expand {f : Object → ℝ} :
    ∑ x : Object, f x = f .green_square + f .blue_circle + f .green_circle := by
  change (Finset.univ : Finset Object).sum f = _
  have : (Finset.univ : Finset Object) = {.green_square, .blue_circle, .green_circle} :=
    by native_decide
  rw [this]
  simp [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton]
  ring

@[simp] private theorem Utterance.sum_expand {f : Utterance → ℝ} :
    ∑ x : Utterance, f x = f .square + f .circle + f .green + f .blue := by
  change (Finset.univ : Finset Utterance).sum f = _
  have : (Finset.univ : Finset Utterance) = {.square, .circle, .green, .blue} :=
    by native_decide
  rw [this]
  simp [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton]
  ring

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

set_option maxHeartbeats 800000 in
/-- σ_aU agrees: "square" > "green" for green_square. -/
theorem σ_aU_green_sq :
    σ_aU_cfg.S1 () .green_square .square > σ_aU_cfg.S1 () .green_square .green := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- σ_aU agrees: "circle" > "green" for green_circle (cost breaks symmetry). -/
theorem σ_aU_green_circ :
    σ_aU_cfg.S1 () .green_circle .circle > σ_aU_cfg.S1 () .green_circle .green := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- The S1 scores for "blue" and "circle" at blue_circle are exactly equal under σ_aU.
    Both compute to exp(1/2): "blue" has L0 = 1 and cost = 1/2 (so arg = 1 - 1/2),
    while "circle" has L0 = 1/2 and cost = 0 (so arg = 1/2 - 0).
    This is why `rsa_predict` cannot handle this case — interval arithmetic
    approximates exp(1/2) independently for each utterance, yielding overlapping
    intervals. The proof instead shows exact score equality and lifts to policy. -/
private theorem σ_aU_score_blue_eq_circle :
    (σ_aU_cfg.S1agent ()).score .blue_circle .blue =
    (σ_aU_cfg.S1agent ()).score .blue_circle .circle := by
  simp only [RSAConfig.S1agent, actionGoalScore,
             RSAConfig.L0agent, RationalAction.policy, RationalAction.totalScore,
             adjCost, uniformPrior, Utterance.appliesTo,
             Object.sum_expand, Utterance.sum_expand]
  norm_num

/-- σ_aU fails: "blue" and "circle" are tied for blue_circle.
    This is the key prediction that distinguishes σ_aU from σ_bU.
    Under belief-oriented scoring (σ_bU), the log transform amplifies the
    informativity advantage of "blue" (L0 = 1) over "circle" (L0 = 1/2);
    under action-oriented scoring (σ_aU), the raw difference is exactly
    offset by cost. -/
theorem σ_aU_blue_circ_tie :
    ¬(σ_aU_cfg.S1 () .blue_circle .blue > σ_aU_cfg.S1 () .blue_circle .circle) ∧
    ¬(σ_aU_cfg.S1 () .blue_circle .circle > σ_aU_cfg.S1 () .blue_circle .blue) := by
  have heq : σ_aU_cfg.S1 () .blue_circle .blue = σ_aU_cfg.S1 () .blue_circle .circle :=
    RationalAction.policy_eq_of_score_eq _ _ _ _ σ_aU_score_blue_eq_circle
  exact ⟨fun h => absurd heq (ne_of_gt h), fun h => absurd heq.symm (ne_of_gt h)⟩

-- §13b. σ_bS: Belief-oriented, salience belief
-- Agrees on green_sq; reverses on both blue_circ and green_circ.
-- Worst speaker model (1/3).

set_option maxHeartbeats 800000 in
/-- σ_bS agrees: "square" > "green" for green_square.
    The unique shape word wins regardless of speaker belief, since "square"
    applies to only one object while "green" is ambiguous. -/
theorem σ_bS_green_sq :
    σ_bS_cfg.S1 () .green_square .square > σ_bS_cfg.S1 () .green_square .green := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- σ_bS reverses blue_circle: predicts "circle" > "blue".
    With salience-weighted L0, blue_circle has the highest salience (139),
    so L0(blue_circ|"circle") = 139/169 ≈ 0.82, making "circle" quite
    informative. Combined with zero cost for "circle" vs cost 1/2 for "blue",
    the pragmatic advantage of "blue" is overcome. -/
theorem σ_bS_blue_circ_reversal :
    σ_bS_cfg.S1 () .blue_circle .circle > σ_bS_cfg.S1 () .blue_circle .blue := by
  rsa_predict

set_option maxHeartbeats 800000 in
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

set_option maxHeartbeats 800000 in
/-- σ_aS agrees: "square" > "green" for green_square. -/
theorem σ_aS_green_sq :
    σ_aS_cfg.S1 () .green_square .square > σ_aS_cfg.S1 () .green_square .green := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- σ_aS reverses blue_circle: predicts "circle" > "blue".
    Same mechanism as σ_bS: salience inflates L0(blue_circ|"circle") = 139/169.
    Under action-oriented scoring, this raw probability advantage
    (plus zero cost) overcomes "blue"'s informativity. -/
theorem σ_aS_blue_circ_reversal :
    σ_aS_cfg.S1 () .blue_circle .circle > σ_aS_cfg.S1 () .blue_circle .blue := by
  rsa_predict

set_option maxHeartbeats 800000 in
/-- σ_aS agrees: "circle" > "green" for green_circle.
    Unlike σ_bS, the action-oriented scoring doesn't amplify the L0
    advantage of "green" via log, so cost wins for green_circle. -/
theorem σ_aS_green_circ :
    σ_aS_cfg.S1 () .green_circle .circle > σ_aS_cfg.S1 () .green_circle .green := by
  rsa_predict

-- §13d. Capstone: σ_bU is the best speaker model

/-- σ_bU uniquely predicts "blue" > "circle" for blue_circle.

    The blue_circle observation is the decisive test: 36/42 speakers chose "blue"
    over "circle" (Table 3). σ_bU is the only model that predicts this:
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

/-- The RSA model accounts for all 6 qualitative findings from Q&F (2015). -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact speaker_prefers_unique_shape
  · exact speaker_prefers_unique_color
  · exact cost_breaks_symmetry
  · exact no_cost_symmetry
  · exact salience_reversal_circle
  · exact salience_reversal_green

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
   most comparisons; the σ_aU tie requires manual score-equality proof
   (exp/log don't cancel in action-oriented scoring). The capstone theorem
   shows σ_bU uniquely predicts the blue_circle observation.
-/

end Phenomena.Reference.Studies.QingFranke2015
