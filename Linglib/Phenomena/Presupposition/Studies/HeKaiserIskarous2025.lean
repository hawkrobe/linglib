/-
# He, Kaiser & Iskarous (2025): Sentence Polarity Asymmetries

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

## Reference

He, M., Kaiser, E., & Iskarous, K. (2025). "Modeling sentence polarity asymmetries:
Fuzzy interpretations in a possibly wonky world". SCiL 2025.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FinEnum

namespace Phenomena.Presupposition.Studies.HeKaiserIskarous2025

-- State Model

/-- Two states for part-whole relations.

    - `pos`: The positive state (A has B)
    - `neg`: The negative state (A doesn't have B) -/
inductive HKIState where
  | pos : HKIState  -- A has B
  | neg : HKIState  -- A doesn't have B
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr, Inhabited

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

end HeKaiserIskarous2025
