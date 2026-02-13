import Linglib.Core.Empirical

/-!
# Goodman & Stuhlmuller (2013) — Empirical Data

"Knowledge and Implicature: Modeling Language Understanding as Social Cognition"
Topics in Cognitive Science 5(1): 173-184

## Paradigm

Three objects that may have a property. Speaker observes a subset (access = 1, 2,
or 3) and makes a quantified or numeral statement. Listener divides $100 among
world states (0-3 objects have property). Speaker access is common knowledge.

Trials with knowledgeability bet <= 70 excluded from primary analysis.

## What Theories Predict About

For each (word, access) condition, a theory should predict the listener's posterior
over world states. The `BetComparison` data records whether bets on one state
significantly exceeded bets on another — the observable that posteriors map to.

## References

- Goodman, N.D. & Stuhlmuller, A. (2013). Knowledge and Implicature.
  *Topics in Cognitive Science* 5(1): 173-184.
-/

namespace Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013

open Phenomena

-- ============================================================================
-- Metadata
-- ============================================================================

def citation : String :=
  "Goodman & Stuhlmuller (2013). Topics in Cognitive Science 5(1): 173-184."

def measure : MeasureSpec :=
  { scale := .continuous, task := .forcedChoice, unit := "dollars (out of $100)" }

def nPerExperiment : Nat := 50
def nObjects : Nat := 3

-- ============================================================================
-- Core Data: Pairwise Bet Comparisons
-- ============================================================================

/-- A pairwise comparison of bets on two world states in a condition.

The key observable: did participants allocate significantly more money to
world state `stateA` than to `stateB`? A theory that predicts the listener's
posterior P(state | word, access) can be checked against this. -/
structure BetComparison where
  experiment : Nat
  word : String
  /-- How many of 3 objects the speaker observed -/
  access : Nat
  stateA : Nat
  stateB : Nat
  /-- Did bets on stateA significantly exceed bets on stateB? -/
  aExceedsB : Bool
  evidence : String
  deriving Repr

-- ============================================================================
-- Experiment 1: "some" x access (N = 50)
-- ============================================================================

/-- Access = 3: bets on state 2 > bets on state 3. -/
def exp1_some_a3_2v3 : BetComparison :=
  { experiment := 1, word := "some", access := 3, stateA := 2, stateB := 3
    aExceedsB := true, evidence := "t(43) = -10.2, p < .001" }

/-- Access = 1: bets on state 2 did NOT exceed bets on state 3. -/
def exp1_some_a1_2v3 : BetComparison :=
  { experiment := 1, word := "some", access := 1, stateA := 2, stateB := 3
    aExceedsB := false, evidence := "t(31) = 0.77, p = .78" }

/-- Access = 2: bets on state 2 did NOT exceed bets on state 3. -/
def exp1_some_a2_2v3 : BetComparison :=
  { experiment := 1, word := "some", access := 2, stateA := 2, stateB := 3
    aExceedsB := false, evidence := "t(28) = -0.82, p = .21" }

/-- Bets on state 3 at access = 3 significantly lower than at access = 1. -/
def exp1_a3_vs_a1_on_state3 : BetComparison :=
  { experiment := 1, word := "some", access := 3, stateA := 3, stateB := 3
    aExceedsB := false
    evidence := "access 3 < access 1 on state 3: t(47) = -4.0, p < .001" }

-- ============================================================================
-- Experiment 2: number words x access (N = 50)
-- ============================================================================

-- "two"

/-- "two", access = 3: bets on state 2 > bets on state 3. -/
def exp2_two_a3_2v3 : BetComparison :=
  { experiment := 2, word := "two", access := 3, stateA := 2, stateB := 3
    aExceedsB := true, evidence := "t(43) = -10.2, p < .001" }

/-- "two", access = 2: bets on state 2 did NOT exceed bets on state 3. -/
def exp2_two_a2_2v3 : BetComparison :=
  { experiment := 2, word := "two", access := 2, stateA := 2, stateB := 3
    aExceedsB := false, evidence := "t(24) = 1.1, p = .87" }

-- "one"

/-- "one", access = 3: bets on state 1 > bets on state 2. -/
def exp2_one_a3_1v2 : BetComparison :=
  { experiment := 2, word := "one", access := 3, stateA := 1, stateB := 2
    aExceedsB := true, evidence := "t(42) = -13.1, p < .001" }

/-- "one", access = 3: bets on state 1 > bets on state 3. -/
def exp2_one_a3_1v3 : BetComparison :=
  { experiment := 2, word := "one", access := 3, stateA := 1, stateB := 3
    aExceedsB := true, evidence := "t(42) = -17.1, p < .001" }

/-- "one", access = 1: bets on state 1 did NOT exceed bets on state 2. -/
def exp2_one_a1_1v2 : BetComparison :=
  { experiment := 2, word := "one", access := 1, stateA := 1, stateB := 2
    aExceedsB := false, evidence := "t(24) = 1.9, p = .96" }

/-- "one", access = 1: bets on state 1 did NOT exceed bets on state 3. -/
def exp2_one_a1_1v3 : BetComparison :=
  { experiment := 2, word := "one", access := 1, stateA := 1, stateB := 3
    aExceedsB := false, evidence := "t(24) = 3.2, p = 1.0" }

/-- "one", access = 2: bets on state 1 > bets on state 3 (partial). -/
def exp2_one_a2_1v3 : BetComparison :=
  { experiment := 2, word := "one", access := 2, stateA := 1, stateB := 3
    aExceedsB := true, evidence := "t(25) = -3.9, p < .001" }

/-- "one", access = 2: bets on state 1 did NOT exceed bets on state 2. -/
def exp2_one_a2_1v2 : BetComparison :=
  { experiment := 2, word := "one", access := 2, stateA := 1, stateB := 2
    aExceedsB := false, evidence := "t(25) = 1.5, p = .92" }

-- ============================================================================
-- Omnibus Effects
-- ============================================================================

structure OmnibusTest where
  description : String
  testType : String
  statistic : Float
  p : Float
  deriving Repr

def exp1_access_effect : OmnibusTest :=
  { description := "Effect of access on bets on state 3"
    testType := "one-way ANOVA, F(2, 102)", statistic := 10.18, p := 0.001 }

def exp2_access_main : OmnibusTest :=
  { description := "Main effect of access"
    testType := "ANOVA, F(2, 205)", statistic := 6.57, p := 0.01 }

def exp2_word_main : OmnibusTest :=
  { description := "Main effect of word"
    testType := "ANOVA, F(2, 205)", statistic := 269.8, p := 0.001 }

def exp2_interaction : OmnibusTest :=
  { description := "Word x access interaction"
    testType := "ANOVA, F(1, 205)", statistic := 34.7, p := 0.001 }

-- ============================================================================
-- Manipulation Check
-- ============================================================================

structure KnowledgeabilityCheck where
  access : Nat
  meanBet : Float
  sd : Float
  deriving Repr

def knowledge_a1 : KnowledgeabilityCheck := { access := 1, meanBet := 27.1, sd := 4.9 }
def knowledge_a2 : KnowledgeabilityCheck := { access := 2, meanBet := 34.8, sd := 5.7 }
def knowledge_a3 : KnowledgeabilityCheck := { access := 3, meanBet := 93.0, sd := 2.7 }

end Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013
