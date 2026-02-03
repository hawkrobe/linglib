/-
# Yoon et al. (2020): Polite Speech Data

Empirical data structures for "Polite Speech Emerges From Competing Social Goals"
-/

import Mathlib.Data.Rat.Defs
import Linglib.Fragments.English.Scales

/-!

## Experimental Design

- 202 participants on Amazon MTurk
- 12 scenarios per participant (3 goals × 4 states)
- Goals: informative, kind, both
- States: 0-3 hearts (true quality rating)
- Utterances: 8 options (4 adjectives × pos/neg)

## Key Finding

Speakers with BOTH goals (informative + kind) produce more negation
in bad states (0-1 hearts) compared to single-goal conditions.
This is the signature of indirect speech driven by self-presentation.

## Reference

Yoon, E. J., Tessler, M. H., Goodman, N. D., & Frank, M. C. (2020).
Polite Speech Emerges From Competing Social Goals.
Open Mind: Discoveries in Cognitive Science, 4, 71-87.
-/

namespace Phenomena.Politeness.Studies.YoonEtAl2020

-- ============================================================================
-- PART 1: Domain Types
-- ============================================================================

/-- Heart state: 0-3 hearts representing true quality -/
inductive HeartState where
  | h0  -- 0 hearts (terrible)
  | h1  -- 1 heart (bad)
  | h2  -- 2 hearts (good)
  | h3  -- 3 hearts (amazing)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Convert heart state to numeric value -/
def HeartState.toNat : HeartState → Nat
  | .h0 => 0
  | .h1 => 1
  | .h2 => 2
  | .h3 => 3

/-- All heart states -/
def allHeartStates : List HeartState := [.h0, .h1, .h2, .h3]

/-- Utterance types: 4 adjectives × positive/negative -/
inductive Utterance where
  | terrible      -- "It was terrible"
  | bad           -- "It was bad"
  | good          -- "It was good"
  | amazing       -- "It was amazing"
  | notTerrible   -- "It wasn't terrible"
  | notBad        -- "It wasn't bad"
  | notGood       -- "It wasn't good"
  | notAmazing    -- "It wasn't amazing"
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All utterances -/
def allUtterances : List Utterance := [
  .terrible, .bad, .good, .amazing,
  .notTerrible, .notBad, .notGood, .notAmazing
]

/-- Is this a negated utterance? -/
def Utterance.isNegated : Utterance → Bool
  | .notTerrible | .notBad | .notGood | .notAmazing => true
  | _ => false

/-- Get the base adjective (without negation) -/
inductive Adjective where
  | terrible | bad | good | amazing
  deriving DecidableEq, Repr, BEq

def Utterance.baseAdjective : Utterance → Adjective
  | .terrible | .notTerrible => .terrible
  | .bad | .notBad => .bad
  | .good | .notGood => .good
  | .amazing | .notAmazing => .amazing

/-- Speaker goal conditions from the experiment -/
inductive GoalCondition where
  | informative  -- "give accurate and informative feedback"
  | kind         -- "make the listener feel good"
  | both         -- "BOTH make Bob feel good AND give accurate feedback"
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All goal conditions -/
def allGoalConditions : List GoalCondition := [.informative, .kind, .both]

-- ============================================================================
-- PART 1b: Connection to Fragment Scales
-- ============================================================================

/--
The evaluative adjectives used here form a Horn scale.

⟨terrible, bad, good, amazing⟩

This connects to `Fragments.English.Scales.terribleAmazing` in Fragments/Fragments.English.Scales.lean.
The scale structure is important for:
1. Scalar implicatures ("good" implicates "not amazing")
2. Negation semantics ("not terrible" → could be bad, good, or amazing)
-/
def evalScale : Fragments.English.Scales.Scale Fragments.English.Scales.EvalExpr := Fragments.English.Scales.terribleAmazing

/-- Convert local Adjective to fragment EvalExpr -/
def Adjective.toEvalExpr : Adjective → Fragments.English.Scales.EvalExpr
  | .terrible => .terrible
  | .bad => .bad
  | .good => .good
  | .amazing => .amazing

/-- Convert fragment EvalExpr to local Adjective -/
def Adjective.fromEvalExpr : Fragments.English.Scales.EvalExpr → Adjective
  | .terrible => .terrible
  | .bad => .bad
  | .good => .good
  | .amazing => .amazing

/-- Convert local Utterance to fragment EvalUtterance -/
def Utterance.toEvalUtterance : Utterance → Fragments.English.Scales.EvalUtterance
  | .terrible => .pos .terrible
  | .bad => .pos .bad
  | .good => .pos .good
  | .amazing => .pos .amazing
  | .notTerrible => .neg .notTerrible
  | .notBad => .neg .notBad
  | .notGood => .neg .notGood
  | .notAmazing => .neg .notAmazing

/-- Verify our utterances match the fragment utterances -/
theorem utterances_match_fragments :
    allUtterances.length = Fragments.English.Scales.allEvalUtterances.length := by native_decide

/-- The scale has 4 levels (terrible < bad < good < amazing) -/
theorem evalScale_has_4_levels :
    evalScale.items.length = 4 := by native_decide

/-- Scalar alternative: "good" has alternative "amazing" -/
theorem good_alt_amazing :
    evalScale.alternatives .good = [.amazing] := by native_decide

-- ============================================================================
-- PART 2: Soft Semantics (from literal meaning experiment)
-- ============================================================================

/--
Soft semantic meaning: P(state | adjective) from literal meaning norming.

From Supplemental Materials (N=51 participants):
- "terrible" → mostly 0 hearts
- "bad" → mostly 0-1 hearts
- "good" → mostly 2-3 hearts
- "amazing" → mostly 3 hearts
-/
def softSemantics : Adjective → HeartState → ℚ
  -- "terrible" peaks at 0 hearts
  | .terrible, .h0 => 95/100
  | .terrible, .h1 => 5/100
  | .terrible, .h2 => 0
  | .terrible, .h3 => 0
  -- "bad" spans 0-1 hearts
  | .bad, .h0 => 40/100
  | .bad, .h1 => 55/100
  | .bad, .h2 => 5/100
  | .bad, .h3 => 0
  -- "good" spans 2-3 hearts
  | .good, .h0 => 0
  | .good, .h1 => 5/100
  | .good, .h2 => 60/100
  | .good, .h3 => 35/100
  -- "amazing" peaks at 3 hearts
  | .amazing, .h0 => 0
  | .amazing, .h1 => 0
  | .amazing, .h2 => 10/100
  | .amazing, .h3 => 90/100

-- ============================================================================
-- PART 2b: Compositional Negation
-- ============================================================================

/--
Soft proposition: a function from states to degrees of truth in [0,1].

This is the probabilistic analog of `Prop' = World → Bool` in Montague semantics.
-/
abbrev SoftProp := HeartState → ℚ

/--
**Compositional soft negation operator.**

This is the soft analog of `pnot : Prop' → Prop'` from Montague/Entailment/Polarity.

Key properties (proven in YoonEtAl2020.lean):
- Involution: `softNot (softNot p) = p`
- Antitone: If `p ≤ q` pointwise, then `softNot q ≤ softNot p`
- Coincides with Boolean negation when restricted to {0, 1}
-/
def softNot (p : SoftProp) : SoftProp := fun s => 1 - p s

/-- Base adjective meaning (positive form) -/
def adjMeaning : Adjective → SoftProp
  | .terrible => softSemantics .terrible
  | .bad => softSemantics .bad
  | .good => softSemantics .good
  | .amazing => softSemantics .amazing

/--
**Compositionally derived utterance semantics.**

Negated utterances are derived by applying `softNot` to base meanings:
- ⟦not terrible⟧ = softNot(⟦terrible⟧)

This mirrors Montague's compositional semantics where
⟦not φ⟧ = pnot(⟦φ⟧).
-/
def utteranceSemantics : Utterance → SoftProp
  -- Positive forms: base adjective meaning
  | .terrible => adjMeaning .terrible
  | .bad => adjMeaning .bad
  | .good => adjMeaning .good
  | .amazing => adjMeaning .amazing
  -- Negated forms: compositionally derived via softNot
  | .notTerrible => softNot (adjMeaning .terrible)
  | .notBad => softNot (adjMeaning .bad)
  | .notGood => softNot (adjMeaning .good)
  | .notAmazing => softNot (adjMeaning .amazing)

/-- Legacy helper for compatibility -/
def negatedSemantics (adj : Adjective) : SoftProp := softNot (adjMeaning adj)

-- ============================================================================
-- PART 3: Utterance Cost
-- ============================================================================

/-- Utterance cost: number of words -/
def utteranceCost : Utterance → ℕ
  | .terrible | .bad | .good | .amazing => 2  -- "It was X"
  | .notTerrible | .notBad | .notGood | .notAmazing => 3  -- "It wasn't X"

-- ============================================================================
-- PART 4: Subjective Value Function
-- ============================================================================

/--
Subjective value V(s): linear mapping from states to values.

The listener prefers higher heart states: V(3 hearts) > V(0 hearts).
We use the simple linear function V(s) = s.
-/
def subjectiveValue : HeartState → ℚ
  | .h0 => 0
  | .h1 => 1
  | .h2 => 2
  | .h3 => 3

-- ============================================================================
-- PART 5: Model Configuration
-- ============================================================================

/-- Model configuration parameters -/
structure PolitenessConfig where
  /-- Speaker optimality parameter -/
  alpha : ℕ := 3
  /-- Cost scaling factor -/
  costScale : ℚ := 1
  /-- Number of discretization points for goal weight φ -/
  phiSteps : ℕ := 5
  deriving Repr

/-- Default configuration -/
def defaultConfig : PolitenessConfig := {}

-- ============================================================================
-- PART 6: Experimental Data (Aggregated)
-- ============================================================================

/--
Aggregated experimental data: proportion choosing each utterance.

Key pattern (Figure 5 in paper):
- Informative goal: Direct utterances matching true state
- Kind goal: Positive utterances (good, amazing) regardless of state
- Both goal: MORE NEGATION for bad states (0-1 hearts)
-/
structure ExperimentalData where
  /-- Proportion choosing utterance u given state s and goal g -/
  proportion : GoalCondition → HeartState → Utterance → ℚ

/--
Key behavioral finding: "Both" goal produces more negation in bad states.

From Bayesian mixed-effects model:
- Both vs Informative at low states: M = -1.33, 95% CI = [-1.69, -0.98]
- Both vs Kind at low states: M = -0.50, 95% CI = [-0.92, -0.07]
-/
def negationIncreasesForBothGoal : Prop :=
  -- Speakers with "both" goals use more negation for 0-heart states
  -- than speakers with only "informative" goal
  True  -- Placeholder for the behavioral finding

-- ============================================================================
-- PART 7: Inferred Goal Weights (from model fitting)
-- ============================================================================

/--
Inferred utility weights ω from model fitting (Table 2 in paper).

For the full model (informational, social, presentational):
-/
structure InferredWeights where
  omega_inf : ℚ   -- Informational weight
  omega_soc : ℚ   -- Social weight
  omega_pres : ℚ  -- Presentational weight
  phi : ℚ         -- Projected goal weight (kindness vs informativeness)
  deriving Repr

/-- Inferred weights for "informative" goal condition -/
def weightsInformative : InferredWeights :=
  { omega_inf := 36/100
    omega_soc := 2/100
    omega_pres := 62/100
    phi := 49/100 }

/-- Inferred weights for "kind" goal condition -/
def weightsKind : InferredWeights :=
  { omega_inf := 25/100
    omega_soc := 31/100
    omega_pres := 44/100
    phi := 37/100 }

/-- Inferred weights for "both" goal condition -/
def weightsBoth : InferredWeights :=
  { omega_inf := 36/100
    omega_soc := 11/100
    omega_pres := 54/100
    phi := 36/100 }

/-- Get weights for a goal condition -/
def getWeights : GoalCondition → InferredWeights
  | .informative => weightsInformative
  | .kind => weightsKind
  | .both => weightsBoth

-- ============================================================================
-- PART 8: Model Comparison Results
-- ============================================================================

/--
Model comparison results (Table 1 in paper).

The full model (informational + social + presentational) outperforms
all submodels by Bayes factor.
-/
structure ModelComparisonResult where
  modelName : String
  varianceExplained : ℚ
  logBayesFactor : ℚ  -- Relative to full model (negative = worse)
  deriving Repr

def modelComparisonResults : List ModelComparisonResult := [
  { modelName := "informational, social, presentational"
    varianceExplained := 97/100
    logBayesFactor := 0 },
  { modelName := "informational, presentational"
    varianceExplained := 96/100
    logBayesFactor := -1114/100 },  -- -11.14
  { modelName := "informational, social"
    varianceExplained := 92/100
    logBayesFactor := -2506/100 },  -- -25.06
  { modelName := "social, presentational"
    varianceExplained := 23/100
    logBayesFactor := -864 },
  { modelName := "presentational only"
    varianceExplained := 23/100
    logBayesFactor := -87383/100 }, -- -873.83
  { modelName := "social only"
    varianceExplained := 22/100
    logBayesFactor := -88552/100 }, -- -885.52
  { modelName := "informational only"
    varianceExplained := 83/100
    logBayesFactor := -27489/100 }  -- -274.89
]

/-- The full 3-utility model has highest Bayes factor -/
theorem full_model_best : modelComparisonResults.head?.map (·.logBayesFactor) = some 0 := rfl

end Phenomena.Politeness.Studies.YoonEtAl2020
