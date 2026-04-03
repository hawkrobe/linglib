import Linglib.Core.Semantics.Proposition
import Linglib.Theories.Semantics.Montague.Types
import Linglib.Theories.Semantics.Entailment.Polarity
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FinEnum

/-!
# Sentence Polarity Asymmetries
@cite{he-kaiser-iskarous-2025}

Empirical data and domain types for modeling sentence polarity asymmetries
with fuzzy interpretations in a possibly wonky world.

## Key Phenomena

Two asymmetries between positive and negative polarity:

1. **Cost asymmetry**: Negation elicits higher production cost than positive polarity
2. **Presupposition asymmetry**: Negation presupposes prominence of its positive
   counterpart in common ground, but not vice versa

## Domain

Part-whole relations (e.g., house-bathroom, classroom-stove):
- States: s_pos (A has B), s_neg (A doesn't have B)
- Utterances: u_pos, u_neg, u_null
- Costs: Cost(u_null)=0, Cost(u_pos)=1, Cost(u_neg)=2

## Models

| Model | Description |
|-------|-------------|
| Standard RSA | Baseline with Boolean semantics |
| fuzzyRSA | Soft semantics with polarity-specific interpretation |
| wonkyRSA | Complex prior for common ground update |
| funkyRSA | Combination of fuzzy + wonky |

-/

namespace Phenomena.Presupposition.Studies.HeKaiserIskarous2025

-- State Model

/-- Two states for part-whole relations.

    - `pos`: The positive state (A has B)
    - `neg`: The negative state (A doesn't have B) -/
inductive HKIState where
  | pos : HKIState  -- A has B
  | neg : HKIState  -- A doesn't have B
  deriving DecidableEq, Repr, Inhabited

instance : Fintype HKIState where
  elems := {.pos, .neg}
  complete := λ x => by cases x <;> simp

instance : FinEnum HKIState :=
  FinEnum.ofList [.pos, .neg] (λ x => by cases x <;> simp)

/-- All states -/
def allStates : List HKIState := [.pos, .neg]

theorem allStates_length : allStates.length = 2 := rfl

-- Utterance Types

/-- Three utterances for part-whole communication.

    - `uPos`: "A has B" (positive polarity, cost 1)
    - `uNeg`: "A doesn't have B" (negative polarity, cost 2)
    - `uNull`: Say nothing (cost 0) -/
inductive HKIUtterance where
  | uPos : HKIUtterance   -- "A has B"
  | uNeg : HKIUtterance   -- "A doesn't have B"
  | uNull : HKIUtterance  -- Say nothing
  deriving DecidableEq, Repr, Inhabited

instance : Fintype HKIUtterance where
  elems := {.uPos, .uNeg, .uNull}
  complete := λ x => by cases x <;> simp

instance : FinEnum HKIUtterance :=
  FinEnum.ofList [.uPos, .uNeg, .uNull] (λ x => by cases x <;> simp)

/-- All utterances -/
def allUtterances : List HKIUtterance := [.uPos, .uNeg, .uNull]

theorem allUtterances_length : allUtterances.length = 3 := rfl

/-- Sentence polarity -/
inductive Polarity where
  | positive : Polarity
  | negative : Polarity
  | null : Polarity
  deriving DecidableEq, Repr

/-- Get polarity of an utterance -/
def HKIUtterance.polarity : HKIUtterance → Polarity
  | .uPos => .positive
  | .uNeg => .negative
  | .uNull => .null

-- Cost Structure

/-- Utterance costs from the paper.

    Cost(u_null) = 0
    Cost(u_pos) = 1
    Cost(u_neg) = 2

    Negation has higher cost due to marked form / longer linguistic realization. -/
def utteranceCost : HKIUtterance → ℚ
  | .uNull => 0
  | .uPos => 1
  | .uNeg => 2

/-- Negative utterances cost more than positive (Asymmetry Hypothesis 1) -/
theorem neg_costs_more : utteranceCost .uNeg > utteranceCost .uPos := by
  native_decide

-- Literal Semantics (Boolean)

/-- Boolean literal semantics: which utterance is true in which state.

    - u_pos is true only in s_pos
    - u_neg is true only in s_neg
    - u_null is true in both (vacuously) -/
def literalTruth : HKIState → HKIUtterance → Bool
  | .pos, .uPos => true
  | .pos, .uNeg => false
  | .pos, .uNull => true
  | .neg, .uPos => false
  | .neg, .uNeg => true
  | .neg, .uNull => true

-- Wonky World Types

/-- World types for wonkyRSA.

    - `normal`: Prior reflects actual world knowledge
    - `wonky`: Uniform prior (speaker's utterance choice is "odd") -/
inductive WorldType where
  | normal : WorldType
  | wonky : WorldType
  deriving DecidableEq, Repr, Inhabited

/-- All world types -/
def allWorldTypes : List WorldType := [.normal, .wonky]

theorem allWorldTypes_length : allWorldTypes.length = 2 := rfl

-- Prior Structure

/-- Prior probability over states.

    In the He et al. study, priors were normed empirically for
    81 part-whole pairs (e.g., house-bathroom has high prior,
    classroom-stove has low prior). -/
structure HKIPrior where
  /-- P(s_pos) - probability of positive state -/
  p_pos : ℚ
  /-- Non-negative -/
  h_pos_nonneg : 0 ≤ p_pos
  /-- At most 1 -/
  h_pos_le_one : p_pos ≤ 1

/-- P(s_neg) = 1 - P(s_pos) -/
def HKIPrior.p_neg (prior : HKIPrior) : ℚ := 1 - prior.p_pos

/-- Get prior probability of a state -/
def HKIPrior.prob (prior : HKIPrior) : HKIState → ℚ
  | .pos => prior.p_pos
  | .neg => prior.p_neg

/-- Uniform prior: P(s_pos) = P(s_neg) = 0.5 -/
def uniformPrior : HKIPrior where
  p_pos := 1/2
  h_pos_nonneg := by native_decide
  h_pos_le_one := by native_decide

/-- High prior: P(s_pos) = 0.9 (typical part, e.g., house-bathroom) -/
def highPrior : HKIPrior where
  p_pos := 9/10
  h_pos_nonneg := by native_decide
  h_pos_le_one := by native_decide

/-- Low prior: P(s_pos) = 0.1 (atypical part, e.g., classroom-stove) -/
def lowPrior : HKIPrior where
  p_pos := 1/10
  h_pos_nonneg := by native_decide
  h_pos_le_one := by native_decide

-- Fuzzy Semantics Parameters

/-- Parameters for fuzzy interpretation functions.

    For negative utterances: constant probability n
    For positive utterances: sigmoid function with parameters (L, k, x0, c) -/
structure FuzzyParams where
  /-- Negative interpretation: [[u_neg]](s_neg) = n -/
  n : ℚ
  /-- Sigmoid maximum value -/
  L : ℚ
  /-- Sigmoid steepness -/
  k : ℚ
  /-- Sigmoid midpoint -/
  x0 : ℚ
  /-- Sigmoid vertical shift -/
  c : ℚ
  /-- n in [0,1] -/
  h_n_valid : 0 ≤ n ∧ n ≤ 1

/-- Best-fit parameters from the paper (Section 4.2).

    n = 0.8, α = 1, θ = {L=0.7, k=6, x0=0.35, c=0.3} -/
def bestFitFuzzyParams : FuzzyParams where
  n := 4/5        -- 0.8
  L := 7/10       -- 0.7
  k := 6
  x0 := 7/20      -- 0.35
  c := 3/10       -- 0.3
  h_n_valid := by constructor <;> native_decide

-- Model Configuration

/-- Configuration for RSA model instances -/
structure HKIConfig where
  /-- Prior over states -/
  prior : HKIPrior
  /-- Rationality parameter -/
  alpha : ℕ := 1
  /-- Wonkiness prior P(wonky) for wonkyRSA -/
  p_wonky : ℚ := 1/2
  /-- Fuzzy parameters for fuzzyRSA -/
  fuzzyParams : FuzzyParams := bestFitFuzzyParams

/-- Default configuration with uniform prior -/
def defaultConfig : HKIConfig where
  prior := uniformPrior

/-- High-prior configuration (typical parts like house-bathroom) -/
def highPriorConfig : HKIConfig where
  prior := highPrior

/-- Low-prior configuration (atypical parts like classroom-stove) -/
def lowPriorConfig : HKIConfig where
  prior := lowPrior

-- Key Theoretical Claims

/-- Asymmetry Hypothesis 1: Negation has higher production cost.

    Marked forms like negation use more complex structures and longer
    linguistic forms, eliciting higher production cost. -/
def asymmetryHypothesis1 : String :=
  "Marked forms like negation elicit higher production cost than " ++
  "their unmarked positive-polarity counterparts."

/-- Asymmetry Hypothesis 2: Negation presupposes positive prominence.

    Negation presupposes that its positive-polarity counterpart is
    relevant or prominent in common ground, but not vice versa. -/
def asymmetryHypothesis2 : String :=
  "Negation presupposes that its positive-polarity counterpart is " ++
  "relevant or prominent in the common ground, not the other way around."

-- ============================================================================
-- Part II: RSA Compositional Grounding
-- ============================================================================

/-- Simple sigmoid approximation using rational arithmetic. -/
def sigmoidApprox (x : ℚ) (L k x0 c : ℚ) : ℚ :=
  let threshold := if k > 0 then 1 / k else 1/10
  if x < x0 - threshold then
    c
  else if x > x0 + threshold then
    L + c
  else
    let slope := L / (2 * threshold)
    let midpoint := c + L / 2
    midpoint + slope * (x - x0)

/-- Fuzzy interpretation for negative utterances.
    [[u_neg]](s_neg) = n (constant)
    [[u_neg]](s_pos) = 1 - n -/
def fuzzyNegInterpretation (n : ℚ) : HKIState → ℚ
  | .neg => n
  | .pos => 1 - n

/-- Fuzzy interpretation for positive utterances. -/
def fuzzyPosInterpretation (p_pos : ℚ) (params : FuzzyParams) : HKIState → ℚ :=
  let sig := sigmoidApprox p_pos params.L params.k params.x0 params.c
  λ s => match s with
    | .pos => sig
    | .neg => 1 - sig

/-- Fuzzy interpretation for null utterance (no information). -/
def fuzzyNullInterpretation : HKIState → ℚ
  | _ => 1

/-- Combined fuzzy meaning function for fuzzyRSA. -/
def fuzzyMeaning (cfg : HKIConfig) (u : HKIUtterance) (s : HKIState) : ℚ :=
  match u with
  | .uNeg => fuzzyNegInterpretation cfg.fuzzyParams.n s
  | .uPos => fuzzyPosInterpretation cfg.prior.p_pos cfg.fuzzyParams s
  | .uNull => fuzzyNullInterpretation s

/-- World-conditioned prior for wonkyRSA. -/
def worldConditionedPrior (cfg : HKIConfig) : WorldType → HKIState → ℚ
  | .wonky, _ => 1/2
  | .normal, s => cfg.prior.prob s

/-- Goal projection for wonkyRSA. -/
def wonkyGoalProject : WorldType → HKIState → HKIState → Bool
  | _, s1, s2 => s1 == s2

/-- Standard scenario has correct dimensions. -/
theorem standard_dimensions :
    allUtterances.length = 3 ∧
    allStates.length = 2 :=
  ⟨rfl, rfl⟩

/-- wonkyRSA has 2 goals (normal, wonky). -/
theorem wonky_dimensions :
    allWorldTypes.length = 2 :=
  rfl

/-- Negative utterances have higher cost in our model. -/
theorem neg_higher_cost :
    utteranceCost .uNeg > utteranceCost .uPos := by
  native_decide

/-- fuzzyRSA with low prior: positive utterance becomes less reliable. -/
theorem fuzzy_low_prior_effect :
    fuzzyMeaning lowPriorConfig .uPos .pos <
    fuzzyMeaning highPriorConfig .uPos .pos := by
  native_decide

/-- Negative interpretation is constant regardless of prior. -/
theorem neg_interpretation_constant :
    fuzzyMeaning lowPriorConfig .uNeg .neg =
    fuzzyMeaning highPriorConfig .uNeg .neg :=
  rfl

/-- Map He et al.'s sentence polarity to compositional context polarity. -/
def toContextPolarity : Polarity → Semantics.Entailment.Polarity.ContextPolarity
  | .positive => .upward
  | .negative => .downward
  | .null => .upward

/-- Cost aligns with UE/DE distinction: DE costs more. -/
theorem cost_reflects_polarity :
    utteranceCost .uPos < utteranceCost .uNeg := by
  native_decide

-- ============================================================================
-- § Compositional Analysis of He et al. Sentences
-- ============================================================================

section CompositionalGrounding

open Semantics.Montague

/-- A simple model for part-whole relations. -/
inductive PWEntity where
  | house | classroom | bathroom | stove
  deriving DecidableEq, Repr

/-- Part-whole model. -/
def pwModel : Model where
  Entity := PWEntity
  decEq := inferInstance

/-- The "has" relation: which containers have which parts. -/
def has_sem : pwModel.interpTy (.e ⇒ .e ⇒ .t) :=
  λ part container => match container, part with
    | .house, .bathroom => true
    | .classroom, .stove => false
    | _, _ => false

/-- Positive sentence meaning: "A has B". -/
def posMeaning (container part : PWEntity) : pwModel.interpTy .t :=
  has_sem part container

/-- Negative sentence meaning: "A doesn't have B" = neg(has(A, B)). -/
def negMeaning (container part : PWEntity) : pwModel.interpTy .t :=
  neg (posMeaning container part)

/-- Key theorem: negative meaning is compositionally derived via `neg`. -/
theorem neg_is_compositional (container part : PWEntity) :
    negMeaning container part = neg (posMeaning container part) := rfl

theorem house_has_bathroom : posMeaning .house .bathroom = true := rfl
theorem house_doesnt_have_bathroom : negMeaning .house .bathroom = false := rfl
theorem classroom_doesnt_have_stove : negMeaning .classroom .stove = true := rfl

open Semantics.Entailment.Polarity
open Core.Proposition

/-- Lift He et al. sentences to world-indexed propositions. -/
def liftToWorlds (s : HKIState) : BProp HKIState :=
  λ w => w == s

/-- Negative sentence meaning as world-indexed proposition.
    ⟦"A doesn't have B"⟧ = pnot(⟦"A has B"⟧) -/
def negMeaningW : BProp HKIState :=
  Decidable.pnot HKIState (liftToWorlds .pos)

/-- Negation reverses entailment (DE property). -/
theorem pnot_reverses_entailment_HKI (p q : BProp HKIState)
    (h : ∀ w, p w = true → q w = true) :
    ∀ w, Decidable.pnot HKIState q w = true → Decidable.pnot HKIState p w = true :=
  Decidable.pnot_reverses_entailment p q h

/-- The grounded polarity from Entailment.Polarity (uses `pnot`). -/
def negSentencePolarity : GroundedPolarity := negationPolarity

/-- Negative sentences have DE polarity (from Montague's proof). -/
theorem neg_sentence_is_de :
    negSentencePolarity.toContextPolarity = .downward := rfl

/-- Positive sentences have UE polarity (identity = no negation). -/
theorem pos_sentence_is_ue :
    identityPolarity.toContextPolarity = .upward := rfl

/-- Structural complexity: count of functional heads in the derivation. -/
def structuralComplexity : HKIUtterance → ℕ
  | .uNull => 0
  | .uPos => 1
  | .uNeg => 2

/-- Utterance cost equals structural complexity. -/
theorem cost_from_structure :
    ∀ u : HKIUtterance, utteranceCost u = structuralComplexity u := by
  intro u
  cases u <;> rfl

/-- Negation adds exactly one unit of complexity (the Neg functional head). -/
theorem negation_adds_one_head :
    structuralComplexity .uNeg = structuralComplexity .uPos + 1 := rfl

end CompositionalGrounding

end HeKaiserIskarous2025
