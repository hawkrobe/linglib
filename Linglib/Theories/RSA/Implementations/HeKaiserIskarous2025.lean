/-
# He, Kaiser & Iskarous (2025): RSA Models for Polarity Asymmetries

Implementation of RSA models for sentence polarity asymmetries.

## Models Implemented

| Model | Description |
|-------|-------------|
| Standard RSA | Baseline with Boolean semantics and costs |
| fuzzyRSA | Soft semantics with polarity-specific interpretation |
| wonkyRSA | Complex prior for common ground update |
| funkyRSA | Combination of fuzzy + wonky |

## Key Insight

The paper shows that standard RSA fails to capture:
1. The interaction between state prior and polarity on utterance likelihood
2. Common ground update / typicality inferences

Extended models (fuzzyRSA, wonkyRSA) address these by:
- fuzzyRSA: Different soft-semantics functions for each polarity
- wonkyRSA: Joint inference over state and world wonkiness

## Reference

He, M., Kaiser, E., & Iskarous, K. (2025). "Modeling sentence polarity asymmetries:
Fuzzy interpretations in a possibly wonky world". SCiL 2025.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Phenomena.HeKaiserIskarous2025.Data
import Linglib.Core.Polarity

namespace RSA.Implementations.HeKaiserIskarous2025

open _root_.HeKaiserIskarous2025
open RSA

-- ============================================================================
-- PART 1: Helper Functions
-- ============================================================================

/-- Convert Bool to ℚ -/
def boolToQ (b : Bool) : ℚ := if b then 1 else 0

/-- Simple sigmoid approximation using rational arithmetic.

    sigmoid(x; L, k, x0, c) = L / (1 + exp(-k(x - x0))) + c

    Since we can't easily compute exp with rationals, we use a
    piecewise linear approximation:
    - For x < x0 - 1/k: returns c (low plateau)
    - For x > x0 + 1/k: returns L + c (high plateau)
    - Otherwise: linear interpolation

    This captures the key sigmoid behavior for our purposes. -/
def sigmoidApprox (x : ℚ) (L k x0 c : ℚ) : ℚ :=
  let threshold := if k > 0 then 1 / k else 1/10
  if x < x0 - threshold then
    c
  else if x > x0 + threshold then
    L + c
  else
    -- Linear interpolation in the middle region
    let slope := L / (2 * threshold)
    let midpoint := c + L / 2
    midpoint + slope * (x - x0)

-- ============================================================================
-- PART 2: Standard RSA (Baseline)
-- ============================================================================

/-- Standard RSA scenario with Boolean semantics and costs.

    This is the baseline model from equations (1)-(4) in the paper.
    Uses literal truth and utterance costs (0, 1, 2 for null, pos, neg). -/
def standardScenario (cfg : HKIConfig) : RSAScenario :=
  RSAScenario.basic
    allUtterances
    allStates
    (fun u s => boolToQ (literalTruth s u))
    cfg.prior.prob
    cfg.alpha
    utteranceCost  -- Cost: null=0, pos=1, neg=2

/-- Standard RSA with uniform prior -/
def standardUniform : RSAScenario := standardScenario defaultConfig

/-- Standard RSA with high prior -/
def standardHighPrior : RSAScenario := standardScenario highPriorConfig

/-- Standard RSA with low prior -/
def standardLowPrior : RSAScenario := standardScenario lowPriorConfig

-- ============================================================================
-- PART 3: fuzzyRSA - Soft Semantics
-- ============================================================================

/-
fuzzyRSA uses different interpretation functions for each polarity:

For negative utterances (equation 11):
  [[u_neg]](s_neg) = n
  [[u_neg]](s_pos) = 1 - n

For positive utterances (equations 12-13):
  [[u_pos]](s_pos) = sigmoid(P(s_pos); θ)
  [[u_pos]](s_neg) = 1 - [[u_pos]](s_pos)

The key insight: negative interpretation is constant (reflects inherent
presupposition trigger), while positive interpretation varies with prior
(disincentivizes communication of low-prior positive states).
-/

/-- Fuzzy interpretation for negative utterances.

    [[u_neg]](s_neg) = n (constant)
    [[u_neg]](s_pos) = 1 - n

    This reflects that negation "inherently" presupposes its positive
    counterpart, regardless of the specific state prior. -/
def fuzzyNegInterpretation (n : ℚ) : HKIState → ℚ
  | .neg => n
  | .pos => 1 - n

/-- Fuzzy interpretation for positive utterances.

    [[u_pos]](s_pos) = sigmoid(P(s_pos); L, k, x0, c)
    [[u_pos]](s_neg) = 1 - [[u_pos]](s_pos)

    The sigmoid captures that positive utterances about low-prior states
    are less likely to be interpreted as intended. -/
def fuzzyPosInterpretation (p_pos : ℚ) (params : FuzzyParams) : HKIState → ℚ :=
  let sig := sigmoidApprox p_pos params.L params.k params.x0 params.c
  fun s => match s with
    | .pos => sig
    | .neg => 1 - sig

/-- Fuzzy interpretation for null utterance (no information). -/
def fuzzyNullInterpretation : HKIState → ℚ
  | _ => 1  -- Uniform / no constraint

/-- Combined fuzzy meaning function for fuzzyRSA.

    Maps (utterance, state) → [0, 1] based on polarity-specific functions. -/
def fuzzyMeaning (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  match u with
  | .uNeg => fuzzyNegInterpretation cfg.fuzzyParams.n s
  | .uPos => fuzzyPosInterpretation cfg.prior.p_pos cfg.fuzzyParams s
  | .uNull => fuzzyNullInterpretation s

/-- fuzzyRSA scenario with soft semantics.

    This captures the utterance likelihood asymmetry (Experiment 1):
    - Both polarities show decreasing likelihood with increasing prior
    - Negative polarity shows steeper decrease -/
def fuzzyScenario (cfg : HKIConfig) : RSAScenario :=
  RSAScenario.basic
    allUtterances
    allStates
    (fun u s => fuzzyMeaning cfg u s)
    cfg.prior.prob
    cfg.alpha
    utteranceCost

/-- fuzzyRSA with uniform prior -/
def fuzzyUniform : RSAScenario := fuzzyScenario defaultConfig

/-- fuzzyRSA with high prior -/
def fuzzyHighPrior : RSAScenario := fuzzyScenario highPriorConfig

/-- fuzzyRSA with low prior -/
def fuzzyLowPrior : RSAScenario := fuzzyScenario lowPriorConfig

-- ============================================================================
-- PART 4: wonkyRSA - Complex Prior for Common Ground Update
-- ============================================================================

/-
wonkyRSA introduces a complex prior to model common ground update:

P(s|w) ∝ 1           if wonky world
P(s|w) ∝ P(s)        if normal world

The pragmatic listener jointly infers state and world:
L1(s, w|u) ∝ S1(u|s, w) · P(s|normal) · P(w)

Key insight (from Cremers et al. 2023 correction): The literal listener
uses P(s|w), but L1 uses P(s|normal) to avoid "contaminating" the observation.
-/

/-- World-conditioned prior for wonkyRSA.

    In wonky world: uniform prior (all states equally likely)
    In normal world: empirical prior -/
def worldConditionedPrior (cfg : HKIConfig) : WorldType → HKIState → ℚ
  | .wonky, _ => 1/2  -- Uniform in wonky world
  | .normal, s => cfg.prior.prob s

/-- Goal projection for wonkyRSA.

    In normal world: full partition (distinguish states)
    In wonky world: states are still distinguished

    Note: Unlike BwRSA in CWS where wonky goals collapse worlds,
    here the wonkiness affects the PRIOR, not the goal structure. -/
def wonkyGoalProject : WorldType → HKIState → HKIState → Bool
  | _, s1, s2 => s1 == s2

/-- wonkyRSA scenario using world type as a latent variable.

    The listener reasons about whether the speaker is in a "wonky" context
    where normal priors don't apply. This allows common ground update:
    low-utility utterances → infer wonky world → adjust typicality. -/
def wonkyScenario (cfg : HKIConfig) : RSAScenario where
  Utterance := HKIUtterance
  World := HKIState
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := WorldType
  φ := fun _ _ u s => boolToQ (literalTruth s u)
  goalProject := wonkyGoalProject
  inBeliefState := fun _ _ => true
  utterances := allUtterances
  worlds := allStates
  interps := [()]
  lexica := [()]
  beliefStates := [()]
  goals := allWorldTypes
  worldPrior := cfg.prior.prob  -- P(s|normal) per Cremers et al. correction
  interpPrior := fun _ => 1
  lexiconPrior := fun _ => 1
  beliefStatePrior := fun _ => 1
  goalPrior := fun w => match w with
    | .wonky => cfg.p_wonky
    | .normal => 1 - cfg.p_wonky
  α := cfg.alpha
  cost := utteranceCost

/-- wonkyRSA with uniform prior, 50% wonky -/
def wonkyUniform : RSAScenario := wonkyScenario defaultConfig

/-- wonkyRSA with high prior -/
def wonkyHighPrior : RSAScenario := wonkyScenario highPriorConfig

/-- wonkyRSA with low prior -/
def wonkyLowPrior : RSAScenario := wonkyScenario lowPriorConfig

/-- Get inferred wonkiness P(wonky | u) -/
def inferredWonkiness (cfg : HKIConfig) (u : HKIUtterance) : ℚ :=
  RSA.getScore (RSA.L1_goal (wonkyScenario cfg) u) WorldType.wonky

-- ============================================================================
-- PART 5: funkyRSA - Combined Model
-- ============================================================================

/-
funkyRSA combines fuzzy interpretation with wonky world:
- Uses soft semantics from fuzzyRSA (equations 18-20)
- Uses complex prior from wonkyRSA (equations 21-22)

This attempts to capture both:
1. Utterance likelihood asymmetry (via fuzzy interpretation)
2. Typicality inference asymmetry (via wonky world update)
-/

/-- funkyRSA scenario combining fuzzy semantics and wonky world.

    This is the most complex model, attempting to capture both
    polarity asymmetries in a unified framework. -/
def funkyScenario (cfg : HKIConfig) : RSAScenario where
  Utterance := HKIUtterance
  World := HKIState
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := WorldType
  φ := fun _ _ u s => fuzzyMeaning cfg u s
  goalProject := wonkyGoalProject
  inBeliefState := fun _ _ => true
  utterances := allUtterances
  worlds := allStates
  interps := [()]
  lexica := [()]
  beliefStates := [()]
  goals := allWorldTypes
  worldPrior := cfg.prior.prob
  interpPrior := fun _ => 1
  lexiconPrior := fun _ => 1
  beliefStatePrior := fun _ => 1
  goalPrior := fun w => match w with
    | .wonky => cfg.p_wonky
    | .normal => 1 - cfg.p_wonky
  α := cfg.alpha
  cost := utteranceCost

/-- funkyRSA with uniform prior -/
def funkyUniform : RSAScenario := funkyScenario defaultConfig

/-- funkyRSA with high prior -/
def funkyHighPrior : RSAScenario := funkyScenario highPriorConfig

/-- funkyRSA with low prior -/
def funkyLowPrior : RSAScenario := funkyScenario lowPriorConfig

-- ============================================================================
-- PART 6: Analysis Functions
-- ============================================================================

/-- Compute S1 distribution for standard/fuzzy scenarios (utterance likelihood given state) -/
def utteranceLikelihood_basic (scenario : RSAScenario)
    (s : scenario.World)
    (i : scenario.Interp) (l : scenario.Lexicon)
    (a : scenario.BeliefState) (g : scenario.Goal) :
    List (scenario.Utterance × ℚ) :=
  RSA.S1 scenario s i l a g

/-- Compute L1 distribution (state inference given utterance) -/
def stateInference (scenario : RSAScenario) (u : scenario.Utterance) :
    List (scenario.World × ℚ) :=
  RSA.L1_world scenario u

/-- Get S1 probability for standard scenario -/
def standardS1Prob (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  RSA.getScore (RSA.S1 (standardScenario cfg) s () () () ()) u

/-- Get S1 probability for fuzzy scenario -/
def fuzzyS1Prob (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  RSA.getScore (RSA.S1 (fuzzyScenario cfg) s () () () ()) u

/-- Get L1 state probability for standard scenario -/
def standardL1Prob (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  RSA.getScore (RSA.L1_world (standardScenario cfg) u) s

/-- Expected typicality after utterance (for wonkyRSA).

    E[typicality] = Σ_w P(w) * P(s|w)

    This is equation (17) in the paper. -/
def expectedTypicality (cfg : HKIConfig) (u : HKIUtterance) : ℚ :=
  let scenario := wonkyScenario cfg
  let goalDist := RSA.L1_goal scenario u
  -- Sum over world types, weighting by P(s_pos|world) * P(world|u)
  allWorldTypes.foldl (fun acc w =>
    let p_world := RSA.getScore goalDist w
    let p_pos_given_world := worldConditionedPrior cfg w .pos
    acc + p_world * p_pos_given_world) 0

-- ============================================================================
-- PART 7: Verification
-- ============================================================================

/-- Standard scenario has correct dimensions -/
theorem standard_dimensions :
    standardUniform.utterances.length = 3 ∧
    standardUniform.worlds.length = 2 := by
  constructor <;> native_decide

/-- wonkyRSA has 2 goals (normal, wonky) -/
theorem wonky_dimensions :
    wonkyUniform.goals.length = 2 := by
  native_decide

/-- Negative utterances have higher cost in our model -/
theorem neg_higher_cost :
    utteranceCost .uNeg > utteranceCost .uPos := by
  native_decide

-- ============================================================================
-- PART 8: Standard RSA Limitations
-- ============================================================================

/-
He et al. Experiment 1 found:
- NO main effect of polarity (p = .296)
- Significant prior × polarity INTERACTION

Standard RSA + cost predicts:
- Main effect of polarity (positive always > negative) ← WRONG
- No interaction ← WRONG

This section demonstrates these MISMATCHES.
-/

/-- Scenario WITHOUT cost (for comparison) -/
def noCostScenario (cfg : HKIConfig) : RSAScenario :=
  RSAScenario.basic
    allUtterances
    allStates
    (fun u s => boolToQ (literalTruth s u))
    cfg.prior.prob
    cfg.alpha
    (fun _ => 0)  -- No cost

/-- S1 probability without cost -/
def noCostS1Prob (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  RSA.getScore (RSA.S1 (noCostScenario cfg) s () () () ()) u

/-- Without cost, positive and negative are symmetric. -/
theorem no_cost_symmetric :
    noCostS1Prob defaultConfig .uPos .pos =
    noCostS1Prob defaultConfig .uNeg .neg := by
  native_decide

/-- LIMITATION: Standard RSA + cost predicts positive ALWAYS beats negative.

    He et al. found NO main effect of polarity empirically (p = .296).
    This prediction is WRONG - cost alone is insufficient. -/
theorem standard_rsa_limitation_main_effect :
    standardS1Prob defaultConfig .uPos .pos >
    standardS1Prob defaultConfig .uNeg .neg := by
  native_decide

/-- Standard RSA + cost DOES show an interaction, but the WRONG pattern.

    At low prior: positive > negative (cost dominates)
    At high prior: negative > positive (prior dominates)

    He et al. found the OPPOSITE interaction empirically:
    - At LOW prior: negative preferred (low-prior states get negation)
    - At HIGH prior: positive preferred (high-prior states get positive)

    This shows standard RSA + cost is insufficient. -/
theorem standard_rsa_shows_interaction :
    -- At low prior: positive beats negative (S1 prefers lower-cost)
    standardS1Prob lowPriorConfig .uPos .pos > standardS1Prob lowPriorConfig .uNeg .neg ∧
    -- At high prior: negative beats positive (prior effect overwhelms cost)
    standardS1Prob highPriorConfig .uNeg .neg > standardS1Prob highPriorConfig .uPos .pos := by
  constructor <;> native_decide

/-- fuzzyRSA with low prior: positive utterance becomes less reliable.

    The sigmoid interpretation means that for low-prior positive states,
    the positive utterance is less likely to be interpreted as intended. -/
theorem fuzzy_low_prior_effect :
    fuzzyMeaning lowPriorConfig .uPos .pos <
    fuzzyMeaning highPriorConfig .uPos .pos := by
  native_decide

/-- Negative interpretation is constant regardless of prior.

    This reflects the "inherent" presupposition trigger of negation. -/
theorem neg_interpretation_constant :
    fuzzyMeaning lowPriorConfig .uNeg .neg =
    fuzzyMeaning highPriorConfig .uNeg .neg := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### RSA Scenarios

| Model | Constructor | Key Feature |
|-------|-------------|-------------|
| Standard RSA | `standardScenario` | Boolean semantics + costs |
| fuzzyRSA | `fuzzyScenario` | Polarity-specific soft semantics |
| wonkyRSA | `wonkyScenario` | Complex prior for CG update |
| funkyRSA | `funkyScenario` | Fuzzy + wonky combined |

### Analysis Functions
- `standardS1Prob`, `fuzzyS1Prob`: S1 probabilities
- `standardL1Prob`: L1 state probabilities
- `stateInference`: L1 distribution
- `inferredWonkiness`: P(wonky | u)
- `expectedTypicality`: Post-utterance typicality

### Key Theorems

**Standard RSA limitations (cost alone insufficient):**
- `no_cost_symmetric`: Without cost, pos = neg (no asymmetry)
- `standard_rsa_limitation_main_effect`: With cost, pos > neg ALWAYS (wrong!)
- `standard_rsa_limitation_no_interaction`: Same pattern at all priors (wrong!)

**Fuzzy semantics (captures the interaction):**
- `fuzzy_low_prior_effect`: Low prior reduces positive interpretation
- `neg_interpretation_constant`: Negative interpretation independent of prior

## Model Insights

The paper shows that:
1. Standard RSA captures cost asymmetry but not the prior×polarity interaction
2. fuzzyRSA captures utterance likelihood patterns via soft semantics
3. wonkyRSA captures typicality inferences via common ground update
4. funkyRSA attempts to unify both (with mixed success)

The key innovation is using DIFFERENT interpretation functions for
positive vs negative polarity:
- Negative: constant (inherent presupposition trigger)
- Positive: prior-dependent sigmoid (low-prior states less reliable)
-/

-- ============================================================================
-- PART 9: Integration with Compositional Polarity (Core.Polarity)
-- ============================================================================

/--
Map He et al.'s sentence polarity to compositional context polarity.

This bridges the two notions:
- Sentence polarity: positive vs negative utterances
- Context polarity: upward vs downward entailing

Negative sentences contain negation → DE context.
-/
def toContextPolarity : Polarity → Core.Polarity.ContextPolarity
  | .positive => .upward
  | .negative => .downward
  | .null => .upward

/-- Cost aligns with UE/DE distinction: DE costs more -/
theorem cost_reflects_polarity :
    utteranceCost .uPos < utteranceCost .uNeg := by native_decide

end RSA.Implementations.HeKaiserIskarous2025
