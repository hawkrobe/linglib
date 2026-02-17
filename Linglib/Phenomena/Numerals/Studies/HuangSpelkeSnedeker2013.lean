import Linglib.Core.Empirical

/-!
# Huang, Spelke & Snedeker (2013) — Covered-Box Paradigm

"What Exactly do Numbers Mean?"
Language Learning and Development 9(2): 105-129

## Design

The covered-box task cancels scalar implicatures by embedding the target term
in a definite description ("the box with two fish") and providing three options:
a visible mismatch, a visible lower-bounded match, and a covered (hidden) box.
When no exact match is visible, choosing the covered box implies the participant
requires an exact match (rejecting the LB-compatible visible option).

The task is validated by a scalar control: "some" in the same paradigm yields
lower-bounded readings (adults accept ALL as "some"), confirming that implicatures
are successfully cancelled.

## Key Empirical Findings

Across 4 experiments with adults and two-knower children (ages 2;6–3;7):

1. **"some" control**: lower-bounded when implicature cancelled — adults accept
   the total set (87% Exp 1, 60% Exp 4), children accept it (83–90%)
2. **"two" critical**: exact under the same conditions — both adults (92–100%)
   and two-knowers (80–95%) reject the 3-fish box, choose covered
3. **Scalar–numeral divergence**: "some" and "two" pattern differently in the
   same implicature-cancelling context; scalars go LB, numerals stay exact
4. **Two-knower specificity**: children who know "one" and "two" but NOT "three"
   still give exact readings for "two"

## References

- Huang, Y.T., Spelke, E., & Snedeker, J. (2013). What exactly do numbers mean?
  *Language Learning and Development* 9(2), 105-129.
- Wynn, K. (1992). Children's acquisition of the number words and the counting
  system. *Cognitive Psychology* 24, 220-251.
- Musolino, J. (2004). The semantics and acquisition of number words. *Cognition* 93.
-/

namespace Phenomena.Numerals.Studies.HuangSpelkeSnedeker2013

open Phenomena

-- ============================================================================
-- Section 1: Task and Measures
-- ============================================================================

/-- Choice in the covered-box paradigm. -/
inductive BoxChoice where
  | mismatch     -- visible box incompatible with description
  | lowerBounded -- visible box satisfying LB but not exact reading
  | covered      -- hidden box (inferred to contain exact match)
  deriving Repr, DecidableEq, BEq

/-- Interpretation measure. -/
def measure : MeasureSpec :=
  { scale := .proportion, task := .forcedChoice, unit := "percentage" }

-- ============================================================================
-- Section 2: Covered-Box Data
-- ============================================================================

/-- A critical trial result. -/
structure CoveredBoxDatum where
  experiment : Nat
  population : String
  term : String
  /-- Cardinalities in the visible boxes -/
  visibleCounts : List Nat
  /-- Percentage selecting the covered box -/
  coveredPct : Nat
  /-- Percentage selecting the lower-bounded visible match -/
  lbPct : Nat
  note : String
  deriving Repr

-- Number word critical trials (no exact match visible)

def exp1_adults_two : CoveredBoxDatum :=
  { experiment := 1, population := "adults (N=60)"
    term := "two", visibleCounts := [1, 3]
    coveredPct := 100, lbPct := 0
    note := "two(1,3V5): unanimous covered-box selection" }

def exp2_twoKnowers_two : CoveredBoxDatum :=
  { experiment := 2, population := "two-knowers (N=10, ages 2;6–3;5)"
    term := "two", visibleCounts := [1, 3]
    coveredPct := 95, lbPct := 0
    note := "two(1,3V5): two-knowers strongly prefer covered box" }

def exp4_children_two : CoveredBoxDatum :=
  { experiment := 4, population := "two-knowers (N=20, ages 2;6–3;7)"
    term := "two", visibleCounts := [1, 3]
    coveredPct := 80, lbPct := 10
    note := "two(1,3): replicated with two-character displays" }

def exp4_adults_two : CoveredBoxDatum :=
  { experiment := 4, population := "adults (N=50, MTurk)"
    term := "two", visibleCounts := [1, 3]
    coveredPct := 92, lbPct := 7
    note := "two(1,3): MTurk replication confirms pattern" }

-- Scalar control trials (validates implicature cancellation)

def exp1_adults_some : CoveredBoxDatum :=
  { experiment := 1, population := "adults (N=60)"
    term := "some", visibleCounts := [0, 4]
    coveredPct := 13, lbPct := 87
    note := "some(NONE,ALL): adults accept total set → LB reading" }

def exp2_twoKnowers_some : CoveredBoxDatum :=
  { experiment := 2, population := "two-knowers (N=10, ages 2;6–3;5)"
    term := "some", visibleCounts := [0, 4]
    coveredPct := 7, lbPct := 83
    note := "some(NONE,ALL): children accept total set, no implicature" }

def exp4_adults_some : CoveredBoxDatum :=
  { experiment := 4, population := "adults (N=50, MTurk)"
    term := "some", visibleCounts := [0, 4]
    coveredPct := 31, lbPct := 60
    note := "some(NONE,ALL): lower rate than Exp 1, still majority LB" }

-- ============================================================================
-- Section 3: Two-Knower Scale Knowledge
-- ============================================================================

/-- Knower level in the Wynn (1992) acquisition sequence.

An empirical classification: children master numeral meanings one at a time.
A two-knower gives 1 for "one", 2 for "two", and random handfuls for higher
numbers in the Give-N task. -/
inductive KnowerLevel where
  | oneKnower
  | twoKnower
  | threeKnower
  | cpKnower
  deriving Repr, DecidableEq, BEq

/-- Whether a child at a given knower level knows the meaning of a numeral. -/
def knowsNumeral : KnowerLevel → Nat → Bool
  | .oneKnower,   1 => true
  | .twoKnower,   1 => true
  | .twoKnower,   2 => true
  | .threeKnower, 1 => true
  | .threeKnower, 2 => true
  | .threeKnower, 3 => true
  | .cpKnower,    _ => true
  | _,            _ => false

/-- Two-knowers know "two" but not "three".
This is the empirical fact that makes their exact "two" readings informative:
they cannot have derived exactness via scalar implicature against "three". -/
theorem two_knower_knows_two : knowsNumeral .twoKnower 2 = true := rfl
theorem two_knower_lacks_three : knowsNumeral .twoKnower 3 = false := rfl

end Phenomena.Numerals.Studies.HuangSpelkeSnedeker2013
