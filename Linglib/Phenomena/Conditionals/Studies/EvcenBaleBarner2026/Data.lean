import Linglib.Core.Empirical
import Mathlib.Data.Rat.Defs

/-!
# @cite{evcen-bale-barner-2026} — Conditional Perfection Data
@cite{von-fintel-2001} @cite{horn-2000}

Theory-neutral empirical data from two experiments on conditional perfection (CP)
by @cite{evcen-bale-barner-2026}.

## Paradigm

Three-button toy: each button can play a sound. A confederate (who has or has
not tested the buttons) answers a question and produces a conditional like
"If you press the blue button, it will play a dog barking." Participants then
judge whether pressing a *different* button will play the sound, choosing
between "No" (= perfected: the other button does NOT play the sound) and
"Can't tell" (= not perfected).

## Key Findings

1. **QUD** (Experiment 1): Antecedent-focused QUDs ("Which of these buttons
   will play a dog sound?") yield significantly more "No" responses than
   consequent-focused ("What happens when I press the blue button?") or
   neutral ("What happens when I press the buttons?") QUDs.

2. **Speaker knowledge** (Experiment 2): Speakers who have tested all buttons
   (full knowledge) yield far more "No" responses than speakers who tested
   only the mentioned button (partial knowledge).

Both findings support @cite{von-fintel-2001}'s exhaustivity account over
@cite{horn-2000}: perfection tracks the availability of alternatives (made
salient by QUD) and the license to exclude them (from speaker competence).
-/

namespace Phenomena.Conditionals.Studies.EvcenBaleBarner2026

open Phenomena

-- ============================================================================
-- Experimental Conditions
-- ============================================================================

/-- QUD manipulation (Experiment 1).

The question asked *before* the confederate's conditional answer. -/
inductive QUDType where
  /-- "Which of these buttons will play a dog sound?" — antecedent-focus.
  Makes alternative antecedents (other buttons) salient. -/
  | antecedentFocused
  /-- "What happens when I press the blue button?" — consequent-focus.
  Makes consequences of the mentioned button salient, not alternatives. -/
  | consequentFocused
  /-- "What happens when I press the buttons?" — neutral.
  No specific focus on antecedents or consequences. -/
  | neutral
  deriving DecidableEq, BEq, Repr

/-- Speaker knowledge manipulation (Experiment 2).

Whether the confederate has tested all buttons or only the mentioned one. -/
inductive KnowledgeCondition where
  /-- Speaker has pressed each button several times — full knowledge. -/
  | fullKnowledge
  /-- Speaker has pressed only the mentioned button — partial knowledge. -/
  | partialKnowledge
  deriving DecidableEq, BEq, Repr

/-- Response type: binary forced choice. -/
inductive CPResponse where
  /-- "No" — participant infers the other button does NOT play the sound.
  This is the conditional perfection response. -/
  | no
  /-- "Can't tell" — participant does not draw the perfection inference. -/
  | cantTell
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Datum Structure
-- ============================================================================

/-- A conditional perfection data point.

Each datum records the mean percentage of "No" responses (perfection) for a
given experimental condition. The DV is binary (No vs Can't tell), and the
reported value is the proportion choosing "No" across participants and items. -/
structure CPDatum where
  /-- Description of the experimental condition -/
  description : String
  /-- Mean percentage of "No" responses (perfection rate) -/
  perfectionRate : ℚ
  /-- Experiment number (1 or 2) -/
  experiment : Nat
  /-- Number of participants in this condition -/
  n : Nat
  deriving Repr

-- ============================================================================
-- Experiment 1: QUD Manipulation
-- ============================================================================

/-- Experiment 1, antecedent-focused condition.
QUD: "Which of these buttons will play a dog sound?"

This QUD makes alternative antecedents (other buttons) salient, licensing
exhaustification over them. -/
def exp1_antecedentFocused : CPDatum := {
  description := "Antecedent-focused QUD: 'Which buttons play a dog sound?'"
  perfectionRate := 5574 / 10000  -- 55.74%
  experiment := 1
  n := 36
}

/-- Experiment 1, consequent-focused condition.
QUD: "What happens when I press the blue button?"

This QUD makes consequences salient, not alternative antecedents.
No exhaustification over other buttons is triggered. -/
def exp1_consequentFocused : CPDatum := {
  description := "Consequent-focused QUD: 'What happens when I press the blue button?'"
  perfectionRate := 2778 / 10000  -- 27.78%
  experiment := 1
  n := 36
}

/-- Experiment 1, neutral condition.
QUD: "What happens when I press the buttons?"

No specific antecedent or consequent focus. -/
def exp1_neutral : CPDatum := {
  description := "Neutral QUD: 'What happens when I press the buttons?'"
  perfectionRate := 3333 / 10000  -- 33.33%
  experiment := 1
  n := 36
}

-- ============================================================================
-- Experiment 2: Speaker Knowledge
-- ============================================================================

/-- Experiment 2, full knowledge condition.
Speaker has pressed each button several times.

Full knowledge licenses the competence assumption: the speaker knows about
all buttons and chose not to mention the others, so exhaustification yields
exclusion. -/
def exp2_fullKnowledge : CPDatum := {
  description := "Full knowledge: speaker has tested all buttons"
  perfectionRate := 6990 / 10000  -- 69.90%
  experiment := 2
  n := 54
}

/-- Experiment 2, partial knowledge condition.
Speaker has pressed only the mentioned button.

Partial knowledge blocks the competence assumption: the speaker's silence
about other buttons reflects ignorance, not exclusion. -/
def exp2_partialKnowledge : CPDatum := {
  description := "Partial knowledge: speaker has tested only the mentioned button"
  perfectionRate := 2037 / 10000  -- 20.37%
  experiment := 2
  n := 54
}

-- ============================================================================
-- Ordering Theorems
-- ============================================================================

/-- Antecedent-focused QUDs promote perfection more than consequent-focused. -/
theorem antecedentFocused_gt_consequentFocused :
    exp1_antecedentFocused.perfectionRate > exp1_consequentFocused.perfectionRate := by
  native_decide

/-- Antecedent-focused QUDs promote perfection more than neutral. -/
theorem antecedentFocused_gt_neutral :
    exp1_antecedentFocused.perfectionRate > exp1_neutral.perfectionRate := by
  native_decide

/-- Full speaker knowledge promotes perfection more than partial knowledge. -/
theorem fullKnowledge_gt_partialKnowledge :
    exp2_fullKnowledge.perfectionRate > exp2_partialKnowledge.perfectionRate := by
  native_decide

/-- The knowledge effect is larger than the QUD effect.

Full knowledge (69.90%) vs partial knowledge (20.37%) is a 49.53pp difference.
Antecedent-focused (55.74%) vs consequent-focused (27.78%) is a 27.96pp
difference. Speaker knowledge has a larger effect on perfection than QUD type,
consistent with competence being a prerequisite for exhaustification. -/
theorem knowledge_effect_larger_than_qud_effect :
    exp2_fullKnowledge.perfectionRate - exp2_partialKnowledge.perfectionRate >
    exp1_antecedentFocused.perfectionRate - exp1_consequentFocused.perfectionRate := by
  native_decide

end Phenomena.Conditionals.Studies.EvcenBaleBarner2026
