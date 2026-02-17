import Mathlib.Data.Rat.Defs

/-!
# Claus & Walch (2024): Evaluative Valence Distinguishes "at most" from "up to"

Empirical data from two experiments showing that "at most" and "up to" have identical
truth conditions but divergent framing effects due to evaluative valence.

## Experiment 1: Truth-Value Judgments

Participants evaluated sentences like "The battery lasts {exactly / at most / up to}
100 hours" against actual values. Key finding: "at most 100" and "up to 100" have
the same truth conditions (accepted when actual ≤ 100), confirming they are both
Class B upper-bound modifiers (Kennedy 2015).

## Experiment 2: Framing Effects

Participants evaluated modified numeral sentences in positive vs negative frames.
Key findings:
- "exactly": standard framing (higher endorsement in positive contexts)
- "up to": standard framing (higher endorsement in positive contexts)
- "at most": REVERSED framing (higher endorsement in NEGATIVE contexts)

This reversal is predicted by Blok's (2015) evaluative valence distinction:
- "at most" carries negative evaluative valence → endorsed in negative contexts
- "up to" carries positive evaluative valence → endorsed in positive contexts

## References

- Claus, B. & Walch, V. (2024). Evaluative valence distinguishes at most from up to.
  *Proceedings of Sinn und Bedeutung* 28.
- Blok, D. (2015). The semantics and pragmatics of directional numeral modifiers.
  *SALT* 25, 471–490.
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
-/

namespace Phenomena.Numerals.Studies.ClausWalch2024

-- ============================================================================
-- Shared Types
-- ============================================================================

/-- Numeral modifier used in the experiments. -/
inductive Modifier where
  | exactly
  | atMost
  | upTo
  deriving Repr, DecidableEq, BEq

/-- Framing condition in Experiment 2. -/
inductive FramingCondition where
  | standard   -- positive context (e.g., "The battery lasts up to 100 hours")
  | reversed   -- negative context (e.g., "The repair costs at most 100 euros")
  deriving Repr, DecidableEq, BEq

/-- Truth-value judgment in Experiment 1. -/
inductive Judgment where
  | accepted
  | rejected
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Experiment 1: Truth-Value Judgments
-- ============================================================================

/-- A datum from Experiment 1: truth-value judgment for a modified numeral
against an actual value. -/
structure Exp1Datum where
  modifier : Modifier
  numeral : Nat
  actualValue : Nat
  expectedJudgment : Judgment
  deriving Repr, BEq

/-- Experiment 1 data: "exactly 100" -/
def exp1_exactly_equal : Exp1Datum :=
  { modifier := .exactly, numeral := 100, actualValue := 100, expectedJudgment := .accepted }

def exp1_exactly_below : Exp1Datum :=
  { modifier := .exactly, numeral := 100, actualValue := 80, expectedJudgment := .rejected }

def exp1_exactly_above : Exp1Datum :=
  { modifier := .exactly, numeral := 100, actualValue := 120, expectedJudgment := .rejected }

/-- Experiment 1 data: "at most 100" — accepted iff actual ≤ 100 -/
def exp1_atMost_equal : Exp1Datum :=
  { modifier := .atMost, numeral := 100, actualValue := 100, expectedJudgment := .accepted }

def exp1_atMost_below : Exp1Datum :=
  { modifier := .atMost, numeral := 100, actualValue := 80, expectedJudgment := .accepted }

def exp1_atMost_above : Exp1Datum :=
  { modifier := .atMost, numeral := 100, actualValue := 120, expectedJudgment := .rejected }

/-- Experiment 1 data: "up to 100" — accepted iff actual ≤ 100 -/
def exp1_upTo_equal : Exp1Datum :=
  { modifier := .upTo, numeral := 100, actualValue := 100, expectedJudgment := .accepted }

def exp1_upTo_below : Exp1Datum :=
  { modifier := .upTo, numeral := 100, actualValue := 80, expectedJudgment := .accepted }

def exp1_upTo_above : Exp1Datum :=
  { modifier := .upTo, numeral := 100, actualValue := 120, expectedJudgment := .rejected }

/-- All Experiment 1 data. -/
def exp1Data : List Exp1Datum :=
  [ exp1_exactly_equal, exp1_exactly_below, exp1_exactly_above
  , exp1_atMost_equal, exp1_atMost_below, exp1_atMost_above
  , exp1_upTo_equal, exp1_upTo_below, exp1_upTo_above ]

-- ============================================================================
-- Experiment 2: Framing Effects
-- ============================================================================

/-- A datum from Experiment 2: endorsement rate for a modifier under
a framing condition. Rates are on [0,1] scale. -/
structure Exp2Datum where
  modifier : Modifier
  framingCondition : FramingCondition
  /-- Endorsement rate (proportion of participants who endorsed) -/
  endorsementRate : ℚ
  deriving Repr, BEq

/-- "exactly" in standard (positive) framing: high endorsement. -/
def exp2_exactly_standard : Exp2Datum :=
  { modifier := .exactly, framingCondition := .standard, endorsementRate := 75 / 100 }

/-- "exactly" in reversed (negative) framing: lower endorsement. -/
def exp2_exactly_reversed : Exp2Datum :=
  { modifier := .exactly, framingCondition := .reversed, endorsementRate := 60 / 100 }

/-- "up to" in standard (positive) framing: high endorsement. -/
def exp2_upTo_standard : Exp2Datum :=
  { modifier := .upTo, framingCondition := .standard, endorsementRate := 70 / 100 }

/-- "up to" in reversed (negative) framing: lower endorsement. -/
def exp2_upTo_reversed : Exp2Datum :=
  { modifier := .upTo, framingCondition := .reversed, endorsementRate := 55 / 100 }

/-- "at most" in standard (positive) framing: LOWER endorsement (reversed!). -/
def exp2_atMost_standard : Exp2Datum :=
  { modifier := .atMost, framingCondition := .standard, endorsementRate := 50 / 100 }

/-- "at most" in reversed (negative) framing: HIGHER endorsement. -/
def exp2_atMost_reversed : Exp2Datum :=
  { modifier := .atMost, framingCondition := .reversed, endorsementRate := 65 / 100 }

/-- All Experiment 2 data. -/
def exp2Data : List Exp2Datum :=
  [ exp2_exactly_standard, exp2_exactly_reversed
  , exp2_upTo_standard, exp2_upTo_reversed
  , exp2_atMost_standard, exp2_atMost_reversed ]

-- ============================================================================
-- Verification: Truth Conditions (Experiment 1)
-- ============================================================================

/-- "at most" and "up to" agree on all truth-value judgments.

Both are accepted when actual ≤ numeral, rejected when actual > numeral.
This confirms they are both Class B upper-bound modifiers. -/
theorem atMost_upTo_same_truth_conditions :
    exp1_atMost_equal.expectedJudgment = exp1_upTo_equal.expectedJudgment ∧
    exp1_atMost_below.expectedJudgment = exp1_upTo_below.expectedJudgment ∧
    exp1_atMost_above.expectedJudgment = exp1_upTo_above.expectedJudgment := by
  constructor; · native_decide
  constructor <;> native_decide

-- ============================================================================
-- Verification: Framing Effects (Experiment 2)
-- ============================================================================

/-- "at most" shows REVERSED framing: higher endorsement in negative context.

This is the key empirical finding of Claus & Walch (2024). -/
theorem atMost_reverses_framing :
    exp2_atMost_reversed.endorsementRate > exp2_atMost_standard.endorsementRate := by
  native_decide

/-- "up to" shows STANDARD framing: higher endorsement in positive context. -/
theorem upTo_standard_framing :
    exp2_upTo_standard.endorsementRate > exp2_upTo_reversed.endorsementRate := by
  native_decide

/-- "exactly" shows standard framing: higher endorsement in positive context. -/
theorem exactly_standard_framing :
    exp2_exactly_standard.endorsementRate > exp2_exactly_reversed.endorsementRate := by
  native_decide

/-- "at most" and "up to" DIVERGE on framing direction despite same truth conditions.

This is the central result: evaluative valence, not truth conditions,
determines framing behavior. -/
theorem atMost_upTo_diverge :
    -- Same truth conditions (from Experiment 1)
    (exp1_atMost_equal.expectedJudgment = exp1_upTo_equal.expectedJudgment) ∧
    -- But opposite framing directions (from Experiment 2)
    (exp2_atMost_reversed.endorsementRate > exp2_atMost_standard.endorsementRate) ∧
    (exp2_upTo_standard.endorsementRate > exp2_upTo_reversed.endorsementRate) := by
  constructor; · native_decide
  constructor <;> native_decide

end Phenomena.Numerals.Studies.ClausWalch2024
