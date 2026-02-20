import Linglib.Core.Empirical

/-!
# Goodman & Stuhlmuller (2013) — Empirical Data @cite{goodman-stuhlmuller-2013}

"Knowledge and Implicature: Modeling Language Understanding as Social Cognition"
Topics in Cognitive Science 5(1): 173-184

## Paradigm

Three objects that may have a property. Speaker observes a subset (access = 1, 2,
or 3) and makes a quantified or numeral statement. Listener divides $100 among
world states (0-3 objects have property). Speaker access is common knowledge.

Trials with knowledgeability bet <= 70 excluded from primary analysis.

## Qualitative Findings

The paper's central finding: scalar implicature and upper-bounded numeral
interpretations are modulated by speaker knowledge. When the speaker has full
access, listeners draw upper-bounded inferences; when access is partial, these
inferences weaken or disappear.

| # | Finding | Word | Access | Comparison | Evidence |
|---|---------|------|--------|------------|----------|
| 1 | Implicature present | "some" | 3 | state 2 > state 3 | t(43)=-10.2, p<.001 |
| 2 | Implicature canceled | "some" | 1 | state 2 not > state 3 | t(31)=0.77, p=.78 |
| 3 | Implicature canceled | "some" | 2 | state 2 not > state 3 | t(28)=-0.82, p=.21 |
| 4 | Upper-bounded | "two" | 3 | state 2 > state 3 | t(43)=-10.2, p<.001 |
| 5 | Not upper-bounded | "two" | 2 | state 2 not > state 3 | t(24)=1.1, p=.87 |
| 6 | Upper-bounded | "one" | 3 | state 1 > state 2 | t(42)=-13.1, p<.001 |
| 7 | Upper-bounded | "one" | 3 | state 1 > state 3 | t(42)=-17.1, p<.001 |
| 8 | Not upper-bounded | "one" | 1 | state 1 not > state 2 | t(24)=1.9, p=.96 |
| 9 | Not upper-bounded | "one" | 1 | state 1 not > state 3 | t(24)=3.2, p=1.0 |
| 10 | Partial | "one" | 2 | state 1 > state 3 | t(25)=-3.9, p<.001 |
| 11 | Partial | "one" | 2 | state 1 not > state 2 | t(25)=1.5, p=.92 |
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
-- Qualitative Findings
-- ============================================================================

/-- The 11 qualitative findings from Goodman & Stuhlmuller (2013) Experiments 1-2.
    Each finding is a pairwise bet comparison between world states under a specific
    (word, access) condition. -/
inductive Finding where
  -- Experiment 1: "some" x speaker access (Fig 2A)
  /-- Full access: bets on state 2 > state 3 (scalar implicature present).
      Evidence: t(43) = -10.2, p < .001. -/
  | some_full_implicature
  /-- Minimal access (a=1): state 2 does not exceed state 3 (canceled).
      Evidence: t(31) = 0.77, p = .78. -/
  | some_minimal_canceled
  /-- Partial access (a=2): state 2 does not exceed state 3 (canceled).
      Evidence: t(28) = -0.82, p = .21. -/
  | some_partial_canceled
  -- Experiment 2: "two" x speaker access (Fig 2B)
  /-- Full access: "two" -> state 2 > state 3 (upper-bounded reading).
      Evidence: t(43) = -10.2, p < .001. -/
  | two_full_upper_bounded
  /-- Partial access (a=2): state 2 does not exceed state 3 (weakened).
      Evidence: t(24) = 1.1, p = .87. -/
  | two_partial_weakened
  -- Experiment 2: "one" x speaker access (Fig 2B)
  /-- Full access: "one" -> state 1 > state 2.
      Evidence: t(42) = -13.1, p < .001. -/
  | one_full_1v2
  /-- Full access: "one" -> state 1 > state 3.
      Evidence: t(42) = -17.1, p < .001. -/
  | one_full_1v3
  /-- Minimal access (a=1): state 1 does not exceed state 2 (canceled).
      Evidence: t(24) = 1.9, p = .96. -/
  | one_minimal_1v2_canceled
  /-- Minimal access (a=1): state 1 does not exceed state 3 (canceled).
      Evidence: t(24) = 3.2, p = 1.0. -/
  | one_minimal_1v3_canceled
  /-- Partial access (a=2): state 1 > state 3 (partial implicature holds).
      Evidence: t(25) = -3.9, p < .001. -/
  | one_partial_1v3
  /-- Partial access (a=2): state 1 does not exceed state 2 (still canceled).
      Evidence: t(25) = 1.5, p = .92. -/
  | one_partial_1v2_canceled
  deriving DecidableEq, BEq, Repr

/-- All findings from the paper. -/
def findings : List Finding :=
  [.some_full_implicature, .some_minimal_canceled, .some_partial_canceled,
   .two_full_upper_bounded, .two_partial_weakened,
   .one_full_1v2, .one_full_1v3,
   .one_minimal_1v2_canceled, .one_minimal_1v3_canceled,
   .one_partial_1v3, .one_partial_1v2_canceled]

-- ============================================================================
-- Statistical Evidence
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
