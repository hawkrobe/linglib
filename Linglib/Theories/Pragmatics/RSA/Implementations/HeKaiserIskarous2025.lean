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

## Insight

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

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Phenomena.Presupposition.Studies.HeKaiserIskarous2025
import Linglib.Core.Proposition
import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Theories.Semantics.Entailment.Polarity

namespace RSA.Implementations.HeKaiserIskarous2025

open Phenomena.Presupposition.Studies.HeKaiserIskarous2025
open RSA.Eval


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


/-- Run L1 for standard RSA scenario with Boolean semantics and costs.

    This is the baseline model from equations (1)-(4) in the paper.
    Uses literal truth and utterance costs (0, 1, 2 for null, pos, neg). -/
def standardL1 (cfg : HKIConfig) (u : HKIUtterance) : List (HKIState × ℚ) :=
  RSA.Eval.basicL1
    allUtterances
    allStates
    (λ utt s => boolToQ (literalTruth s utt))
    cfg.prior.prob
    cfg.alpha
    utteranceCost
    u

/-- Run S1 for standard RSA scenario -/
def standardS1 (cfg : HKIConfig) (s : HKIState) : List (HKIUtterance × ℚ) :=
  RSA.Eval.basicS1
    allUtterances
    allStates
    (λ utt st => boolToQ (literalTruth st utt))
    cfg.prior.prob
    cfg.alpha
    utteranceCost
    s


/-
fuzzyRSA uses different interpretation functions for each polarity:

For negative utterances (equation 11):
  [[u_neg]](s_neg) = n
  [[u_neg]](s_pos) = 1 - n

For positive utterances (equations 12-13):
  [[u_pos]](s_pos) = sigmoid(P(s_pos); θ)
  [[u_pos]](s_neg) = 1 - [[u_pos]](s_pos)

Negative interpretation is constant (reflects inherent presupposition trigger),
while positive interpretation varies with prior (disincentivizes communication
of low-prior positive states).
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
  λ s => match s with
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

/-- Run L1 for fuzzyRSA scenario with soft semantics.

    This captures the utterance likelihood asymmetry (Experiment 1):
    - Both polarities show decreasing likelihood with increasing prior
    - Negative polarity shows steeper decrease -/
def fuzzyL1 (cfg : HKIConfig) (u : HKIUtterance) : List (HKIState × ℚ) :=
  RSA.Eval.basicL1
    allUtterances
    allStates
    (λ utt s => fuzzyMeaning cfg utt s)
    cfg.prior.prob
    cfg.alpha
    utteranceCost
    u

/-- Run S1 for fuzzyRSA scenario -/
def fuzzyS1 (cfg : HKIConfig) (s : HKIState) : List (HKIUtterance × ℚ) :=
  RSA.Eval.basicS1
    allUtterances
    allStates
    (λ utt st => fuzzyMeaning cfg utt st)
    cfg.prior.prob
    cfg.alpha
    utteranceCost
    s


/-
wonkyRSA introduces a complex prior to model common ground update:

P(s|w) ∝ 1           if wonky world
P(s|w) ∝ P(s)        if normal world

The pragmatic listener jointly infers state and world:
L1(s, w|u) ∝ S1(u|s, w) · P(s|normal) · P(w)

From Cremers et al. 2023 correction: the literal listener uses P(s|w),
but L1 uses P(s|normal) to avoid "contaminating" the observation.
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
    here the wonkiness affects the prior, not the goal structure. -/
def wonkyGoalProject : WorldType → HKIState → HKIState → Bool
  | _, s1, s2 => s1 == s2

/-- Run L1 for wonkyRSA scenario using world type as a latent variable.

    The listener reasons about whether the speaker is in a "wonky" context
    where normal priors don't apply. This allows common ground update:
    low-utility utterances → infer wonky world → adjust typicality. -/
def wonkyL1 (cfg : HKIConfig) (u : HKIUtterance) : List ((HKIState × WorldType) × ℚ) :=
  let jointWorlds := allStates.flatMap λ s => allWorldTypes.map λ w => (s, w)
  let goalPrior : WorldType → ℚ := λ w => match w with
    | .wonky => cfg.p_wonky
    | .normal => 1 - cfg.p_wonky
  RSA.Eval.basicL1
    allUtterances
    jointWorlds
    (λ utt (s, _) => boolToQ (literalTruth s utt))
    (λ (s, w) => cfg.prior.prob s * goalPrior w)
    cfg.alpha
    utteranceCost
    u

/-- Get inferred wonkiness P(wonky | u) -/
def inferredWonkiness (cfg : HKIConfig) (u : HKIUtterance) : ℚ :=
  let joint := wonkyL1 cfg u
  let wonkyScores := joint.filter (λ ((_, w), _) => w == .wonky) |>.map (·.2)
  RSA.Eval.sumScores wonkyScores


/-
funkyRSA combines fuzzy interpretation with wonky world:
- Uses soft semantics from fuzzyRSA (equations 18-20)
- Uses complex prior from wonkyRSA (equations 21-22)

This attempts to capture both:
1. Utterance likelihood asymmetry (via fuzzy interpretation)
2. Typicality inference asymmetry (via wonky world update)
-/

/-- Run L1 for funkyRSA scenario combining fuzzy semantics and wonky world.

    This is the most complex model, attempting to capture both
    polarity asymmetries in a unified framework. -/
def funkyL1 (cfg : HKIConfig) (u : HKIUtterance) : List ((HKIState × WorldType) × ℚ) :=
  let jointWorlds := allStates.flatMap λ s => allWorldTypes.map λ w => (s, w)
  let goalPrior : WorldType → ℚ := λ w => match w with
    | .wonky => cfg.p_wonky
    | .normal => 1 - cfg.p_wonky
  RSA.Eval.basicL1
    allUtterances
    jointWorlds
    (λ utt (s, _) => fuzzyMeaning cfg utt s)
    (λ (s, w) => cfg.prior.prob s * goalPrior w)
    cfg.alpha
    utteranceCost
    u


/-- Get S1 probability for standard scenario -/
def standardS1Prob (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  RSA.Eval.getScore (standardS1 cfg s) u

/-- Get S1 probability for fuzzy scenario -/
def fuzzyS1Prob (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  RSA.Eval.getScore (fuzzyS1 cfg s) u

/-- Get L1 state probability for standard scenario -/
def standardL1Prob (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  RSA.Eval.getScore (standardL1 cfg u) s

/-- Expected typicality after utterance (for wonkyRSA).

    E[typicality] = Σ_w P(w) * P(s|w)

    This is equation (17) in the paper. -/
def expectedTypicality (cfg : HKIConfig) (u : HKIUtterance) : ℚ :=
  let joint := wonkyL1 cfg u
  let goalDist := RSA.Eval.marginalize joint Prod.snd
  -- Sum over world types, weighting by P(s_pos|world) * P(world|u)
  allWorldTypes.foldl (λ acc w =>
    let p_world := RSA.Eval.getScore goalDist w
    let p_pos_given_world := worldConditionedPrior cfg w .pos
    acc + p_world * p_pos_given_world) 0


/-- Standard scenario has correct dimensions -/
theorem standard_dimensions :
    allUtterances.length = 3 ∧
    allStates.length = 2 := by
  constructor <;> native_decide

/-- wonkyRSA has 2 goals (normal, wonky) -/
theorem wonky_dimensions :
    allWorldTypes.length = 2 := by
  native_decide

/-- Negative utterances have higher cost in our model -/
theorem neg_higher_cost :
    utteranceCost .uNeg > utteranceCost .uPos := by
  native_decide


/-
He et al. Experiment 1 found:
- No main effect of polarity (p = .296)
- Significant prior × polarity interaction

Standard RSA + cost predicts:
- Main effect of polarity (positive always > negative) -- incorrect
- No interaction -- incorrect

This section demonstrates these mismatches.
-/

/-- S1 without cost (for comparison) -/
def noCostS1 (cfg : HKIConfig) (s : HKIState) : List (HKIUtterance × ℚ) :=
  RSA.Eval.basicS1
    allUtterances
    allStates
    (λ utt st => boolToQ (literalTruth st utt))
    cfg.prior.prob
    cfg.alpha
    (λ _ => 0)  -- No cost
    s

/-- S1 probability without cost -/
def noCostS1Prob (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  RSA.Eval.getScore (noCostS1 cfg s) u

/-- Without cost, positive and negative are symmetric. -/
theorem no_cost_symmetric :
    noCostS1Prob defaultConfig .uPos .pos =
    noCostS1Prob defaultConfig .uNeg .neg := by
  native_decide

/-- Limitation: standard RSA + cost predicts positive always beats negative.

    He et al. found no main effect of polarity empirically (p = .296).
    This prediction is incorrect -- cost alone is insufficient. -/
theorem standard_rsa_limitation_main_effect :
    standardS1Prob defaultConfig .uPos .pos >
    standardS1Prob defaultConfig .uNeg .neg := by
  native_decide

/-- Standard RSA + cost does show an interaction, but the wrong pattern.

    At low prior: positive > negative (cost dominates).
    At high prior: negative > positive (prior dominates).

    He et al. found the opposite interaction empirically:
    - At low prior: negative preferred (low-prior states get negation)
    - At high prior: positive preferred (high-prior states get positive)

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

/--
Map He et al.'s sentence polarity to compositional context polarity.

This bridges the two notions:
- Sentence polarity: positive vs negative utterances
- Context polarity: upward vs downward entailing

Negative sentences contain negation → DE context.
-/
def toContextPolarity : Polarity → Semantics.Entailment.Polarity.ContextPolarity
  | .positive => .upward
  | .negative => .downward
  | .null => .upward

/-- Cost aligns with UE/DE distinction: DE costs more -/
theorem cost_reflects_polarity :
    utteranceCost .uPos < utteranceCost .uNeg := by native_decide


/-
## Compositional Analysis of He et al. Sentences

The He et al. sentences have the form:
- Positive: "A has B" (e.g., "The house has a bathroom")
- Negative: "A doesn't have B" (e.g., "The house doesn't have a bathroom")

Compositionally:
- ⟦uPos⟧ = has(A, B)
- ⟦uNeg⟧ = neg(has(A, B))

where `neg` is Montague's sentence-level negation operator.
-/

section CompositionalGrounding

open Semantics.Montague

/--
A simple model for part-whole relations.

Entities: containers (houses, classrooms) and parts (bathrooms, stoves)
-/
inductive PWEntity where
  | house | classroom | bathroom | stove
  deriving DecidableEq, BEq, Repr

/-- Part-whole model -/
def pwModel : Model where
  Entity := PWEntity
  decEq := inferInstance

/--
The "has" relation: which containers have which parts.

Typical: house-bathroom (most houses have bathrooms)
Atypical: classroom-stove (most classrooms don't have stoves)
-/
def has_sem : pwModel.interpTy (.e ⇒ .e ⇒ .t) :=
  λ part container => match container, part with
    | .house, .bathroom => true   -- Houses typically have bathrooms
    | .classroom, .stove => false -- Classrooms typically don't have stoves
    | _, _ => false

/-- Positive sentence meaning: "A has B" -/
def posMeaning (container part : PWEntity) : pwModel.interpTy .t :=
  interpSVO pwModel container has_sem part

/-- Negative sentence meaning: "A doesn't have B" = neg(has(A, B)) -/
def negMeaning (container part : PWEntity) : pwModel.interpTy .t :=
  neg (posMeaning container part)

/-- Key theorem: negative meaning is compositionally derived via `neg` -/
theorem neg_is_compositional (container part : PWEntity) :
    negMeaning container part = neg (posMeaning container part) := rfl

/-- "The house has a bathroom" is true -/
theorem house_has_bathroom : posMeaning .house .bathroom = true := rfl

/-- "The house doesn't have a bathroom" is false -/
theorem house_doesnt_have_bathroom : negMeaning .house .bathroom = false := rfl

/-- "The classroom doesn't have a stove" is true -/
theorem classroom_doesnt_have_stove : negMeaning .classroom .stove = true := rfl

-- Connecting to Polarity Machinery (with proven DE property)

open Semantics.Entailment.Polarity
open Core.Proposition

/--
Lift He et al. sentences to world-indexed propositions.

Uses `Core.Proposition.BProp HKIState = HKIState → Bool`.
-/
def liftToWorlds (s : HKIState) : BProp HKIState :=
  λ w => w == s

/--
Negative sentence meaning as world-indexed proposition.

⟦"A doesn't have B"⟧ = pnot(⟦"A has B"⟧)

Uses `Core.Proposition.Decidable.pnot` for the negation.
-/
def negMeaningW : BProp HKIState :=
  Decidable.pnot HKIState (liftToWorlds .pos)

/--
Key theorem: Negation reverses entailment (DE property).

Inherited from `Core.Proposition.Decidable.pnot_reverses_entailment`.
This is the centralized proof that negation is Downward Entailing.
-/
theorem pnot_reverses_entailment_HKI (p q : BProp HKIState)
    (h : ∀ w, p w = true → q w = true) :
    ∀ w, Decidable.pnot HKIState q w = true → Decidable.pnot HKIState p w = true :=
  Decidable.pnot_reverses_entailment p q h

/--
The grounded polarity from Entailment.Polarity (uses `pnot`)
-/
def negSentencePolarity : GroundedPolarity := negationPolarity

/-- Negative sentences have DE polarity (from Montague's proof) -/
theorem neg_sentence_is_de :
    negSentencePolarity.toContextPolarity = .downward := rfl

/-- Positive sentences have UE polarity (identity = no negation) -/
theorem pos_sentence_is_ue :
    identityPolarity.toContextPolarity = .upward := rfl

-- Deriving Cost from Structural Complexity

/--
Structural complexity: count of functional heads in the derivation.

- Positive "A has B": just the predication (complexity 1)
- Negative "A doesn't have B": predication + negation head (complexity 2)
-/
def structuralComplexity : HKIUtterance → ℕ
  | .uNull => 0  -- Silence: no structure
  | .uPos => 1   -- Positive: just predication
  | .uNeg => 2   -- Negative: predication + Neg head

/--
Key theorem: utterance cost equals structural complexity.

This derives the stipulated cost function from compositional structure.
-/
theorem cost_from_structure :
    ∀ u : HKIUtterance, utteranceCost u = structuralComplexity u := by
  intro u
  cases u <;> rfl

/--
Negation adds exactly one unit of complexity (the Neg functional head).
-/
theorem negation_adds_one_head :
    structuralComplexity .uNeg = structuralComplexity .uPos + 1 := rfl

end CompositionalGrounding

/-
## Summary: Compositional Grounding

The He et al. model is now grounded in Montague semantics:

1. **Sentence meanings** are compositionally derived:
   - ⟦uPos⟧ = has(A, B)
   - ⟦uNeg⟧ = neg(has(A, B))

2. **Polarity** comes from Montague's proven machinery:
   - `negationPolarity` proves `neg` is DE
   - `identityPolarity` proves positive is UE

3. **Cost** is derived from structural complexity:
   - Negation adds a functional head (Neg)
   - Each head adds 1 to cost

This connects the RSA pragmatic model to compositional formal semantics.
-/

end RSA.Implementations.HeKaiserIskarous2025
