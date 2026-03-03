import Linglib.Core.Empirical
import Mathlib.Data.Rat.Defs

/-!
# @cite{evcen-bale-barner-2026} — Conditional Perfection Data
@cite{von-fintel-2001} @cite{horn-2000}

Theory-neutral empirical data from three experiments on conditional perfection (CP)
by @cite{evcen-bale-barner-2026}.

## Paradigm

Participants watch short videos in which a character, Mary, presses three buttons
(red, blue, orange), each producing an animal sound audible only to her through
headphones. Another character asks a question, and Mary responds with a conditional
like "If you press the blue button, it will play a dog barking." Participants then
judge whether pressing a *different* button will play the same sound, choosing
among "Yes", "No" (= perfected), and "Can't tell" (= not perfected).

## Key Findings

1. **QUD** (Experiment 1, N=98): Antecedent-focused QUDs ("Which of these buttons
   will play a dog sound?") yield significantly more "No" responses (M=0.65) than
   consequent-focused ("What will happen if I press the blue button?", M=0.22) or
   neutral ("What will happen if I press the buttons?", M=0.29) QUDs.
   No significant difference between consequent-focused and neutral (p > .05).
   Two follow-up experiments (each n=32) with alternative antecedent-focused
   phrasings replicate the effect (M=0.86, M=0.77), ruling out a uniqueness
   presupposition explanation.

2. **Overly informative answers** (Experiment 2, N=55): Both optimally informative
   (M=0.92) and overly informative (M=0.84) answers trigger perfection at
   comparable rates under antecedent-focused QUDs (no significant difference,
   p = .16), suggesting overly informative answers are treated as viable
   alternatives for exhaustification.

3. **Speaker knowledge** (Experiment 3, N=72): Speakers who have tested all buttons
   (full knowledge, M=0.72) yield far more "No" responses than speakers who tested
   only two buttons (partial knowledge, M=0.21).

All findings support @cite{von-fintel-2001}'s exhaustivity account over
@cite{horn-2000}: perfection tracks the availability of alternatives (made
salient by QUD) and the license to exclude them (from speaker competence).

Reported values are estimated marginal means from logistic mixed-effects
regressions (on the probability scale), as reported in the paper.
-/

namespace Phenomena.Conditionals.Studies.EvcenBaleBarner2026

open Phenomena

-- ============================================================================
-- Experimental Conditions
-- ============================================================================

/-- QUD manipulation (Experiment 1).

The question asked *before* Mary's conditional answer. -/
inductive QUDType where
  /-- "Which of these buttons will play a dog sound?" — antecedent-focus.
  Makes alternative antecedents (other buttons) salient. -/
  | antecedentFocused
  /-- "What will happen if I press the blue button?" — consequent-focus.
  Makes consequences of the mentioned button salient, not alternatives. -/
  | consequentFocused
  /-- "What will happen if I press the buttons?" — neutral.
  No specific focus on antecedents or consequences. -/
  | neutral
  deriving DecidableEq, BEq, Repr

/-- Answer type manipulation (Experiment 2).

Whether Mary's conditional response matches the QUD's partitioning
(optimally informative) or refers to a strict subset of a QUD cell
(overly informative). -/
inductive AnswerType where
  /-- Answer matches QUD cell, e.g. "If you press the triangles, it will
  play a dog barking" in response to "Which shapes will play a dog sound?" -/
  | optimallyInformative
  /-- Answer is more specific than QUD cell, e.g. "If you press the blue
  square, it will play a dog barking" (a subset of the triangle/square
  partition). -/
  | overlyInformative
  deriving DecidableEq, BEq, Repr

/-- Speaker knowledge manipulation (Experiment 3).

Whether Mary has tested all three buttons or only two of them. -/
inductive KnowledgeCondition where
  /-- Mary pressed and listened to all three buttons — full knowledge. -/
  | fullKnowledge
  /-- Mary pressed and listened to only two buttons — partial knowledge. -/
  | partialKnowledge
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Datum Structure
-- ============================================================================

/-- A conditional perfection data point.

Each datum records the estimated marginal mean proportion of "No" responses
(perfection) for a given experimental condition, from logistic mixed-effects
regression on the probability scale. -/
structure CPDatum where
  /-- Description of the experimental condition -/
  description : String
  /-- Estimated marginal mean proportion of "No" responses (perfection rate) -/
  perfectionRate : ℚ
  /-- Experiment number (1, 2, or 3) -/
  experiment : Nat
  /-- Number of participants (post-exclusion) in the experiment -/
  n : Nat
  deriving Repr

-- ============================================================================
-- Experiment 1: QUD Manipulation (between-subjects, N=98)
-- ============================================================================

/-- Experiment 1 data indexed by QUD type.

Between-subjects: 104 recruited, N=98 post-exclusion, randomly assigned
to one of three conditions. -/
def exp1Data : QUDType → CPDatum
  | .antecedentFocused => {
      description := "Antecedent-focused QUD: 'Which of these buttons will play a dog sound?'"
      perfectionRate := 65 / 100  -- M=0.65, SE=0.10
      experiment := 1
      n := 98 }
  | .consequentFocused => {
      description := "Consequent-focused QUD: 'What will happen if I press the blue button?'"
      perfectionRate := 22 / 100  -- M=0.22, SE=0.10
      experiment := 1
      n := 98 }
  | .neutral => {
      description := "Neutral QUD: 'What will happen if I press the buttons?'"
      perfectionRate := 29 / 100  -- M=0.29, SE=0.11
      experiment := 1
      n := 98 }

/-- Follow-up experiment 1a (n=32): alternative antecedent-focused phrasing.
QUD: "What buttons will play a dog sound?" (omitting "of these").
Replicates the main effect, ruling out a uniqueness presupposition from
"which of these." M=0.86, SE=0.11. -/
def exp1a_whatButtons : CPDatum := {
  description := "Follow-up 1a: 'What buttons will play a dog sound?'"
  perfectionRate := 86 / 100  -- M=0.86
  experiment := 1
  n := 32
}

/-- Follow-up experiment 1b (n=32): alternative antecedent-focused phrasing.
QUD: "Which buttons will play a dog sound?" (omitting "of these").
M=0.77, SE=0.13. -/
def exp1b_whichButtons : CPDatum := {
  description := "Follow-up 1b: 'Which buttons will play a dog sound?'"
  perfectionRate := 77 / 100  -- M=0.77
  experiment := 1
  n := 32
}

-- ============================================================================
-- Experiment 2: Overly Informative Answers (within-subjects, N=55)
-- ============================================================================

/-- Experiment 2 data indexed by answer type.

Within-subjects: 56 recruited, N=55 post-exclusion. Shapes (triangles
and squares in two colors) replace buttons. QUD is always antecedent-focused:
"Which of these shapes, triangles or squares, will play a dog barking?" -/
def exp2Data : AnswerType → CPDatum
  | .optimallyInformative => {
      description := "Optimally informative answer (matches QUD cell)"
      perfectionRate := 92 / 100  -- M=0.92, SE=0.09
      experiment := 2
      n := 55 }
  | .overlyInformative => {
      description := "Overly informative answer (more specific than QUD cell)"
      perfectionRate := 84 / 100  -- M=0.84, SE=0.07
      experiment := 2
      n := 55 }

-- ============================================================================
-- Experiment 3: Speaker Knowledge (within-subjects, N=72)
-- ============================================================================

/-- Experiment 3 data indexed by knowledge condition.

Within-subjects: 75 recruited, N=72 post-exclusion. QUD is always
antecedent-focused. Mary either pressed all three buttons (full knowledge)
or only two (partial knowledge) before making her conditional statement. -/
def exp3Data : KnowledgeCondition → CPDatum
  | .fullKnowledge => {
      description := "Full knowledge: speaker has tested all buttons"
      perfectionRate := 72 / 100  -- M=0.72, SE=0.13
      experiment := 3
      n := 72 }
  | .partialKnowledge => {
      description := "Partial knowledge: speaker has tested only two buttons"
      perfectionRate := 21 / 100  -- M=0.21, SE=0.12
      experiment := 3
      n := 72 }

-- ============================================================================
-- Ordering Theorems
-- ============================================================================

/-- Antecedent-focused QUDs promote perfection more than consequent-focused. -/
theorem antecedentFocused_gt_consequentFocused :
    (exp1Data .antecedentFocused).perfectionRate >
    (exp1Data .consequentFocused).perfectionRate := by native_decide

/-- Antecedent-focused QUDs promote perfection more than neutral. -/
theorem antecedentFocused_gt_neutral :
    (exp1Data .antecedentFocused).perfectionRate >
    (exp1Data .neutral).perfectionRate := by native_decide

/-- Antecedent-focused QUD yields the highest perfection rate across all
QUD types. -/
theorem antecedentFocused_maximizes :
    ∀ q : QUDType,
      (exp1Data .antecedentFocused).perfectionRate ≥
      (exp1Data q).perfectionRate := by
  intro q; cases q <;> simp [exp1Data] <;> native_decide

/-- Consequent-focused and neutral QUDs produce similar (low) perfection
rates: the gap between them (7pp) is smaller than either's gap to
antecedent-focused (43pp, 36pp). The paper reports no significant
difference between these two conditions (p > .05). -/
theorem consequent_neutral_closer_than_antecedent :
    (exp1Data .antecedentFocused).perfectionRate -
    (exp1Data .neutral).perfectionRate >
    (exp1Data .neutral).perfectionRate -
    (exp1Data .consequentFocused).perfectionRate := by native_decide

/-- Follow-up experiments replicate the antecedent-focused effect with
alternative QUD phrasings, ruling out a uniqueness presupposition. -/
theorem followups_replicate :
    exp1a_whatButtons.perfectionRate > (exp1Data .antecedentFocused).perfectionRate ∧
    exp1b_whichButtons.perfectionRate > (exp1Data .antecedentFocused).perfectionRate := by
  constructor <;> native_decide

/-- Both answer types trigger perfection well above chance (> 0.50).
The paper reports no significant difference between them (p = .16),
consistent with both being treated as viable alternatives. -/
theorem both_answer_types_above_chance :
    (exp2Data .optimallyInformative).perfectionRate > 1/2 ∧
    (exp2Data .overlyInformative).perfectionRate > 1/2 := by
  constructor <;> native_decide

/-- Optimally and overly informative answers produce similar perfection
rates: the 8pp gap is small relative to the overall effect size. -/
theorem exp2_rates_close :
    (exp2Data .optimallyInformative).perfectionRate -
    (exp2Data .overlyInformative).perfectionRate < 1/10 := by native_decide

/-- Full speaker knowledge promotes perfection more than partial knowledge. -/
theorem fullKnowledge_gt_partialKnowledge :
    (exp3Data .fullKnowledge).perfectionRate >
    (exp3Data .partialKnowledge).perfectionRate := by native_decide

/-- The knowledge effect is larger than the QUD effect.

Full knowledge (72%) vs partial knowledge (21%) is a 51pp difference.
Antecedent-focused (65%) vs consequent-focused (22%) is a 43pp difference.
Speaker knowledge has a larger effect on perfection than QUD type,
consistent with competence being a prerequisite for exhaustification. -/
theorem knowledge_effect_larger_than_qud_effect :
    (exp3Data .fullKnowledge).perfectionRate -
    (exp3Data .partialKnowledge).perfectionRate >
    (exp1Data .antecedentFocused).perfectionRate -
    (exp1Data .consequentFocused).perfectionRate := by native_decide

end Phenomena.Conditionals.Studies.EvcenBaleBarner2026
