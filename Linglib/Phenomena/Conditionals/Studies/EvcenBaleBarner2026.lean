import Linglib.Features.Acceptability
import Linglib.Paradigms.Measurement
import Mathlib.Data.Rat.Defs
import Linglib.Theories.Semantics.Conditionals.Exhaustivity
import Linglib.Theories.Semantics.Conditionals.Basic
import Linglib.Theories.Pragmatics.Implicature.Competence
import Linglib.Phenomena.ScalarImplicatures.Studies.BaleEtAl2025
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

/-!
# @cite{evcen-bale-barner-2026} — Conditional Perfection
@cite{von-fintel-2001} @cite{horn-2000} @cite{cornulier-1983}

Empirical data from three experiments on conditional perfection (CP)
by @cite{evcen-bale-barner-2026}, plus the bridge connecting these findings to the
answer-level exhaustification theory of conditional perfection.

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

namespace EvcenBaleBarner2026

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

/-- Speaker knowledge manipulation (Experiment 3).

Whether Mary has tested all three buttons or only two of them. -/
inductive KnowledgeCondition where
  /-- Mary pressed and listened to all three buttons — full knowledge. -/
  | fullKnowledge
  /-- Mary pressed and listened to only two buttons — partial knowledge. -/
  | partialKnowledge
  deriving DecidableEq, Repr

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

-- ============================================================================
-- Bridge: Exhaustification Theory → Experimental Predictions
-- ============================================================================

/-!
## Bridge: Exhaustification Theory

Connects the experimental findings to the answer-level exhaustification theory
of conditional perfection.

### Full Argument Chain

The paper's argument proceeds in four steps:

1. **Semantics**: The material conditional "if A then C" does not semantically
   entail the biconditional (established in `Conditionals.Basic`).

2. **Pragmatic mechanism**: Conditional perfection arises from answer-level
   exhaustification (@cite{von-fintel-2001}, following @cite{cornulier-1983}).
   The QUD "which trigger causes C?" makes alternative triggers salient;
   exhaustifying the answer "A causes C" against these alternatives yields
   "only A causes C"; combined with coverage, this entails ¬A → ¬C.

3. **Two prerequisites for perfection**:
   - **QUD**: The QUD must make alternative antecedents salient
     (antecedent-focused), triggering exhaustification.
   - **Speaker competence**: The speaker must be assumed to know about
     the alternative triggers, licensing exclusion of unmentioned alternatives.
   Without either, perfection fails.

4. **Against @cite{horn-2000}**: Horn proposes the alternative to "if A then C"
   is the unconditional "C regardless." This yields only an existential
   inference (some circumstance where ¬C), not the per-trigger universal
   that participants produce. The data support von Fintel's per-trigger
   alternatives.

### Dependency Chain

```
exhaustifiedAnswer (exhIE at answer level)
    ↓ all_alt_innocently_excludable (3-button IE)
exhaustification_yields_perfection (IE + coverage → perfection)
    ↓
theory_chain_3button_perfection (instantiated for experimental scenario)
    ↓
coverage_without_exclusion_insufficient (exclusion is necessary)
vonFintel_strictly_stronger_than_horn (per-trigger > existential)
    ↓
Prediction: perfection iff QUD provides alternatives AND speaker is competent
    ↓
Data: antecedent-focused > neutral ≈ consequent-focused (Exp 1)
      overly informative ≈ optimally informative (Exp 2)
      full knowledge >> partial knowledge (Exp 3)
```
-/

open Semantics.Conditionals
open Core.Order (SimilarityOrdering)
open Semantics.Conditionals.Exhaustivity

private theorem Bool.of_not_eq_true {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b <;> simp_all

-- ============================================================================
-- Section A: 3-Button Experimental Scenario
-- ============================================================================

/-- Triggers in the experimental paradigm: three buttons. -/
inductive Button3Trigger where
  | A | B | C
  deriving DecidableEq, Repr

/-- The 6 possible worlds in a 3-button scenario.

Each world represents pressing one button and observing whether the target
sound plays. -/
inductive Button3World where
  | pressA_plays
  | pressA_silent
  | pressB_plays
  | pressB_silent
  | pressC_plays
  | pressC_silent
  deriving DecidableEq, Repr

instance : Fintype Button3World where
  elems := {.pressA_plays, .pressA_silent, .pressB_plays,
            .pressB_silent, .pressC_plays, .pressC_silent}
  complete := fun x => by cases x <;> simp

/-- Button A is pressed. -/
def pressA : (Button3World → Bool)
  | .pressA_plays | .pressA_silent => true
  | _ => false

/-- The target sound plays. -/
def soundPlays : (Button3World → Bool)
  | .pressA_plays | .pressB_plays | .pressC_plays => true
  | _ => false

/-- Button A causes the target sound. -/
def aCausesSound : (Button3World → Bool)
  | .pressA_plays => true | _ => false

/-- Button B causes the target sound. -/
def bCausesSound : (Button3World → Bool)
  | .pressB_plays => true | _ => false

/-- Button C causes the target sound. -/
def cCausesSound : (Button3World → Bool)
  | .pressC_plays => true | _ => false

/-- Causal relation for the 3-button paradigm: each button causes the
target sound exactly when its associated `*CausesSound` predicate holds. -/
def button3Causes : Button3Trigger → Set Button3World
  | .A => fun w => aCausesSound w = true
  | .B => fun w => bCausesSound w = true
  | .C => fun w => cCausesSound w = true

/-- The salient triggers in the 3-button paradigm: all three buttons. -/
def button3Triggers : Set Button3Trigger := {.A, .B, .C}

-- ============================================================================
-- Section B: Theory Chain — Exhaustification → Perfection (3 Buttons)
-- ============================================================================

/-- **Theory chain: exhaustification yields perfection in the 3-button scenario.**

This instantiates `exhaustification_yields_perfection` for the 3-button
experimental paradigm. With 3 buttons, there are 2 alternative triggers
(B and C). The `all_alt_innocently_excludable` lemma establishes that both
are innocently excludable — the key step that requires the general lemma
rather than the singleton version.

The hypotheses map to experimental conditions:
- `h_exh`: exhaustified answer holds (antecedent-focus QUD + speaker knowledge)
- `h_coverage`: every sound event has a button cause (closed domain)
- `hnp`: button A is not pressed

The IE condition is discharged by `all_alt_innocently_excludable`:
the witness `pressA_plays` establishes consistency of φ ∧ ∀a∈ALT. ¬a
(at pressA_plays, A causes the sound but B and C do not). -/
theorem theory_chain_3button_perfection
    (w : Button3World)
    (h_exh : exhaustifiedAnswer button3Causes button3Triggers .A w)
    (h_coverage : soundPlays w = true →
      ∃ t' ∈ button3Triggers, button3Causes t' w)
    (hnp : pressA w = false) : soundPlays w = false := by
  -- Step 1: Trigger A requires pressing A
  have h_trp : ∀ w', button3Causes .A w' → pressA w' = true := by
    intro w' h; cases w' <;> simp_all [button3Causes, aCausesSound, pressA]
  -- Step 2: All alternative triggers are IE
  -- Apply the general IE criterion (`IsInnocentlyExcludable.of_full_exclusion_consistent`):
  -- every alternative is IE when the prejacent and the negations of all
  -- alternatives are jointly satisfiable. Witness: `pressA_plays` (A causes, B and C do not).
  have h_consist : ∃ w, button3Causes .A w ∧
      ∀ b ∈ answerAlternatives button3Causes button3Triggers .A, ¬ b w := by
    refine ⟨.pressA_plays, rfl, ?_⟩
    intro b hb
    obtain ⟨t'', _, ht''_ne, ht''_eq⟩ := mem_answerAlternatives.mp hb
    cases t'' with
    | A => exact absurd rfl ht''_ne
    | B => rw [← ht''_eq]; simp [button3Causes, bCausesSound]
    | C => rw [← ht''_eq]; simp [button3Causes, cCausesSound]
  have h_ie : ∀ t' ∈ button3Triggers, t' ≠ .A →
      Exhaustification.IsInnocentlyExcludable
        (answerAlternatives button3Causes button3Triggers .A)
        (button3Causes .A)
        (button3Causes t') := by
    intro t' _ht' hne
    have ht'_alt : button3Causes t' ∈
        answerAlternatives button3Causes button3Triggers .A := by
      rw [mem_answerAlternatives]
      cases t' with
      | A => exact absurd rfl hne
      | B => exact ⟨.B, Or.inr (Or.inl rfl), Button3Trigger.noConfusion, rfl⟩
      | C => exact ⟨.C, Or.inr (Or.inr rfl), Button3Trigger.noConfusion, rfl⟩
    exact .of_full_exclusion_consistent ht'_alt h_consist
  -- Step 3: ¬(pressA w = true)
  have h_not_p : ¬(pressA w = true) := by simp [hnp]
  -- Step 4: Apply the theory chain
  have h_not_sound : ¬(soundPlays w = true) :=
    exhaustification_yields_perfection button3Causes button3Triggers .A
      (fun w => pressA w = true) (fun w => soundPlays w = true) w
      h_trp h_ie h_coverage h_exh h_not_p
  exact Bool.of_not_eq_true h_not_sound

-- ============================================================================
-- Section C: Direct Verification (Agrees with Theory Chain)
-- ============================================================================

/-- **Direct verification: exclusion of B and C + ¬pressA → ¬sound.**

Verified by exhaustive case analysis on the 6-world type. Sanity check:
the theory chain agrees with brute-force verification. -/
theorem three_button_perfection :
    ∀ w : Button3World,
      bCausesSound w = false → cCausesSound w = false →
      pressA w = false → soundPlays w = false := by
  native_decide

-- ============================================================================
-- Section D: Horn's Alternative — Why It's Too Weak
-- ============================================================================

/-- What @cite{von-fintel-2001}'s account predicts about non-asserted triggers:
each specific alternative trigger is excluded (universal, per-trigger). -/
def vonFintelPrediction {ι W : Type*}
    (causes : ι → Set W) (triggers : Set ι) (t : ι) (w : W) : Prop :=
  ∀ t' ∈ triggers, t' ≠ t → ¬causes t' w

/-- What @cite{horn-2000}'s account predicts: some non-asserted trigger is
excluded, but we don't know which (existential, unspecified). -/
def hornPrediction {ι W : Type*}
    (causes : ι → Set W) (triggers : Set ι) (t : ι) (w : W) : Prop :=
  ∃ t' ∈ triggers, t' ≠ t ∧ ¬causes t' w

/-- **Von Fintel entails Horn**: per-trigger exclusion implies existential exclusion.

If we know that every specific alternative trigger is excluded (von Fintel),
then certainly some trigger is excluded (Horn). -/
theorem vonFintel_entails_horn
    {ι W : Type*} (causes : ι → Set W) (triggers : Set ι) (t : ι) (w : W)
    (h_other : ∃ t' ∈ triggers, t' ≠ t)
    (h_vf : vonFintelPrediction causes triggers t w) :
    hornPrediction causes triggers t w := by
  obtain ⟨t', ht'_mem, ht'_ne⟩ := h_other
  exact ⟨t', ht'_mem, ht'_ne, h_vf t' ht'_mem ht'_ne⟩

/-- **Horn does NOT entail von Fintel**: existential exclusion does not
determine which trigger is excluded.

Counterexample: in the 3-button scenario at world `pressB_plays`, trigger B
causes the sound and C does not. Horn's prediction holds (C doesn't cause it),
but von Fintel's fails (B *does* cause it). The existential "some other button
doesn't play the sound" is strictly weaker than the universal "each other
button doesn't play the sound."

This is the paper's key argument against Horn: participants respond "No" to
*specific* other buttons (per-trigger judgment), not just "some other button
won't play it." -/
theorem horn_not_entails_vonFintel :
    ∃ (w : Button3World),
      hornPrediction button3Causes button3Triggers .A w ∧
      ¬vonFintelPrediction button3Causes button3Triggers .A w := by
  -- At pressB_plays: B causes sound (✓), C doesn't (✓)
  -- Horn: ∃ t'≠A, ¬causes t' → C. ✓
  -- von Fintel: ∀ t'≠A, ¬causes t' → B causes sound. ✗
  refine ⟨.pressB_plays, ?_, ?_⟩
  · exact ⟨.C, Or.inr (Or.inr rfl), Button3Trigger.noConfusion,
      by simp [button3Causes, cCausesSound]⟩
  · intro h
    have := h .B (Or.inr (Or.inl rfl)) Button3Trigger.noConfusion
    simp [button3Causes, bCausesSound] at this

/-- **Von Fintel is strictly stronger than Horn.**

Combining the two: von Fintel's per-trigger alternatives generate strictly
stronger predictions than Horn's unconditional alternative. The 3-button
paradigm discriminates between the two accounts. -/
theorem vonFintel_strictly_stronger_than_horn :
    -- von Fintel → Horn (forward direction)
    (∀ w : Button3World, vonFintelPrediction button3Causes button3Triggers .A w →
      hornPrediction button3Causes button3Triggers .A w) ∧
    -- Horn ↛ von Fintel (backward direction fails)
    (∃ w : Button3World, hornPrediction button3Causes button3Triggers .A w ∧
      ¬vonFintelPrediction button3Causes button3Triggers .A w) := by
  constructor
  · intro w h
    exact vonFintel_entails_horn button3Causes button3Triggers .A w
      ⟨.B, Or.inr (Or.inl rfl), Button3Trigger.noConfusion⟩ h
  · exact horn_not_entails_vonFintel

-- ============================================================================
-- Section E: Theory Predicts Asymmetry
-- ============================================================================

/-- **Without exclusion, perfection fails.**

Coverage alone (every C-event has some trigger) does NOT yield ¬p → ¬C.
Witness: a scenario where trigger t requires p but trigger t' fires at ¬p-worlds.
Coverage holds, but ¬p ∧ C.

This is the other half of the theory's prediction: perfection requires
exclusion (from exhaustification), not just coverage. Without exclusion
(e.g., consequent-focus QUD or partial speaker knowledge), the theory predicts
no perfection — matching the experimental findings. -/
theorem coverage_without_exclusion_insufficient :
    ∃ (W Trigger : Type)
      (causes : Trigger → W → Prop) (triggers : Set Trigger)
      (t : Trigger) (_ : t ∈ triggers)
      (p C : W → Prop),
      (∀ w, causes t w → p w) ∧
      (∀ w, C w → ∃ t' ∈ triggers, causes t' w) ∧
      (∃ w, ¬p w ∧ C w) := by
  refine ⟨Bool, Bool, (fun trigger world => world = trigger), Set.univ,
          true, Set.mem_univ _, (· = true), (fun _ => True), ?_, ?_, ?_⟩
  · intro w h; exact h
  · intro w _; exact ⟨w, Set.mem_univ w, rfl⟩
  · exact ⟨false, Bool.false_ne_true, trivial⟩

-- ============================================================================
-- Section F: Prerequisites for Exhaustification
-- ============================================================================

/-- Whether a QUD makes alternative antecedents salient.

Antecedent-focused QUDs ("Which button will play a dog sound?") partition
the answer space by antecedent, making alternative triggers salient for
exhaustification. Consequent-focused and neutral QUDs do not. -/
def qudProvidesAlternatives : QUDType → Bool
  | .antecedentFocused => true
  | .consequentFocused => false
  | .neutral => false

/-- Whether a speaker's epistemic state licenses the competence assumption.

When the speaker has tested all buttons (full knowledge), the hearer can
assume competence: the speaker's silence about other buttons is informative,
licensing exclusion. With partial knowledge, silence reflects ignorance. -/
def speakerCompetenceAssumed : KnowledgeCondition → Bool
  | .fullKnowledge => true
  | .partialKnowledge => false

/-- **Exhaustification is licensed iff both prerequisites hold.**

The theory predicts perfection only when:
1. The QUD makes alternative antecedents salient (→ alternatives for Exh)
2. The speaker is assumed competent (→ exclusion of alternatives)

This is derived from the conjunction of the two independent prerequisites,
not stipulated as a single function. -/
def exhaustificationLicensed (knowledge : KnowledgeCondition) (qud : QUDType) : Bool :=
  qudProvidesAlternatives qud && speakerCompetenceAssumed knowledge

/-- With antecedent-focused QUD and full knowledge, exhaustification is licensed. -/
theorem licensed_with_both :
    exhaustificationLicensed .fullKnowledge .antecedentFocused = true := rfl

/-- With consequent-focused QUD, exhaustification is not licensed
(even with full knowledge) — because the QUD doesn't provide alternatives. -/
theorem not_licensed_without_qud :
    exhaustificationLicensed .fullKnowledge .consequentFocused = false := rfl

/-- With partial knowledge, exhaustification is not licensed
(even with antecedent-focused QUD) — because competence isn't assumed. -/
theorem not_licensed_without_knowledge :
    exhaustificationLicensed .partialKnowledge .antecedentFocused = false := rfl

-- ============================================================================
-- Section G: Data Confirms the Predicted Asymmetry
-- ============================================================================

/-- **Data confirms: antecedent-focused QUD promotes perfection.**

The theory predicts higher perfection under antecedent-focused QUDs (which
make alternative triggers salient, licensing exhaustification) than under
consequent-focused or neutral QUDs (which don't). Experiment 1 confirms
both orderings, and antecedent-focused maximizes across all QUD types. -/
theorem antecedentFocused_highest :
    (exp1Data .antecedentFocused).perfectionRate >
    (exp1Data .consequentFocused).perfectionRate ∧
    (exp1Data .antecedentFocused).perfectionRate >
    (exp1Data .neutral).perfectionRate := by
  constructor <;> native_decide

/-- **Data confirms: overly informative answers trigger perfection.**

The theory predicts that if exhaustification operates over QUD-relevant
alternatives, both optimally and overly informative answers should trigger
perfection (since both are answers to the QUD). Experiment 2 confirms:
both types yield high perfection rates with no significant difference. -/
theorem overlyInformative_also_triggers_perfection :
    (exp2Data .overlyInformative).perfectionRate > 1/2 ∧
    (exp2Data .optimallyInformative).perfectionRate -
    (exp2Data .overlyInformative).perfectionRate < 1/10 := by
  constructor <;> native_decide

/-- **Data confirms: speaker knowledge promotes perfection.**

The theory predicts higher perfection when the speaker is knowledgeable
(licensing the assumption that unmentioned alternatives are false, hence
exclusion) than when ignorant (no exclusion license). Experiment 3 confirms
with a large effect (51pp difference). -/
theorem fullKnowledge_highest :
    (exp3Data .fullKnowledge).perfectionRate >
    (exp3Data .partialKnowledge).perfectionRate := by
  native_decide

/-- **Theory predicts the data pattern: perfection is high only when
both prerequisites are met.**

The exhaustification theory predicts perfection should be high only when
`exhaustificationLicensed` returns true (antecedent-focused QUD + full
knowledge). The data confirms: only the antecedent-focused condition (Exp 1)
and the full-knowledge condition (Exp 3) show high perfection rates, while
conditions missing either prerequisite show low rates. -/
theorem high_perfection_matches_licensing :
    -- Licensed conditions produce high perfection (> 50%)
    (exp1Data .antecedentFocused).perfectionRate > 1/2 ∧
    (exp3Data .fullKnowledge).perfectionRate > 1/2 ∧
    -- Unlicensed conditions produce low perfection (< 30%)
    (exp1Data .consequentFocused).perfectionRate < 3/10 ∧
    (exp1Data .neutral).perfectionRate < 3/10 ∧
    (exp3Data .partialKnowledge).perfectionRate < 3/10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Convergent evidence: CP is pragmatic.**

The theory's prediction chain depends entirely on pragmatic factors
(QUD, speaker knowledge, exhaustification). Two independent lines of evidence
confirm the pragmatic nature:

1. **Formal**: `perfection_not_entailed_variablyStrict` proves the biconditional
   is not semantically entailed even under Stalnaker/Lewis variably strict
   semantics — the framework the paper adopts. This is stronger than showing
   it for material implication alone (a weaker semantics could fail to entail
   perfection while a stronger one succeeds).

2. **Experimental**: Perfection rates vary with QUD type and speaker knowledge.
   Semantic entailments are invariant across these factors. -/
theorem cp_is_pragmatic :
    (∃ (W : Type) (sim : SimilarityOrdering W) (domain : Set W)
       (p q : Set W) (w : W),
      variablyStrictImp sim domain p q w ∧ ¬(conditionalPerfection p q w)) ∧
    (exp1Data .antecedentFocused).perfectionRate ≠
    (exp1Data .consequentFocused).perfectionRate ∧
    (exp3Data .fullKnowledge).perfectionRate ≠
    (exp3Data .partialKnowledge).perfectionRate := by
  exact ⟨perfection_not_entailed_variablyStrict, by native_decide, by native_decide⟩

-- ============================================================================
-- Section H: Competence Bridge — CP uses the same mechanism as SI
-- ============================================================================

/-! ## Competence Bridge

The competence assumption in conditional perfection is the same mechanism
formalized in `Implicature.Competence` and tested experimentally by
@cite{bale-etal-2025} for scalar implicatures. Both paradigms:
- Map full speaker knowledge to `BeliefState.disbelief` (speaker knows ¬ψ)
- Map partial knowledge to `BeliefState.noOpinion` (speaker is agnostic)
- Derive strong inference only when competence holds

This section connects `KnowledgeCondition` to the shared infrastructure. -/

open Implicature Implicature.Competence

private abbrev siToBeliefState :=
  BaleEtAl2025.toBeliefState

/-- Map speaker knowledge in the CP paradigm to NeoGricean belief state.

Mirrors `BaleEtAl2025.toBeliefState`: full knowledge → `.disbelief` (speaker
knows ¬ψ for each unmentioned alternative), partial knowledge → `.noOpinion`. -/
def toBeliefStateCP : KnowledgeCondition → BeliefState
  | .fullKnowledge => .disbelief
  | .partialKnowledge => .noOpinion

/-- The CP and SI competence mappings are identical: full knowledge maps to
disbelief and partial knowledge maps to no opinion in both paradigms. -/
theorem competence_mapping_agrees :
    (toBeliefStateCP .fullKnowledge = siToBeliefState .fullKnowledge) ∧
    (toBeliefStateCP .partialKnowledge = siToBeliefState .partialKnowledge) :=
  ⟨rfl, rfl⟩

/-- `speakerCompetenceAssumed` agrees with the NeoGricean `competent` predicate
applied via `toBeliefStateCP`. This connects the study-specific Boolean to
the general implicature infrastructure. -/
theorem speakerCompetence_matches_neoGricean :
    ∀ k : KnowledgeCondition,
      speakerCompetenceAssumed k = competent (toBeliefStateCP k) := by
  intro k; cases k <;> rfl

/-- Full knowledge: `processAlternative` yields a strong inference
(exclusion of unmentioned alternatives is licensed). -/
theorem fk_processAlternative_strong :
    let p := processAlternative true (toBeliefStateCP .fullKnowledge)
    p.weakHolds = true ∧ p.competenceAssumed = true ∧ p.strongDerived = true := by
  native_decide

/-- Partial knowledge: `processAlternative` yields weak-only inference
(exclusion not licensed — silence reflects ignorance, not absence). -/
theorem pk_processAlternative_weak :
    let p := processAlternative true (toBeliefStateCP .partialKnowledge)
    p.weakHolds = true ∧ p.competenceAssumed = false ∧ p.strongDerived = false := by
  native_decide

/-- Cross-domain unity: CP and SI use the same competence-gated exhaustification.

Both @cite{evcen-bale-barner-2026} (conditional perfection) and
@cite{bale-etal-2025} (scalar implicatures) map full knowledge to strong
inference and partial knowledge to weak-only, via the identical
`processAlternative` machinery from `Implicature.Competence`. -/
theorem cp_si_competence_unity :
    -- CP: full knowledge → strong, partial → weak
    (processAlternative true (toBeliefStateCP .fullKnowledge)).strongDerived = true ∧
    (processAlternative true (toBeliefStateCP .partialKnowledge)).strongDerived = false ∧
    -- SI: full knowledge → strong, partial → weak
    (processAlternative true (siToBeliefState .fullKnowledge)).strongDerived = true ∧
    (processAlternative true (siToBeliefState .partialKnowledge)).strongDerived = false := by
  native_decide

-- ============================================================================
-- Section I: ALT Constraint (Footnote 7)
-- ============================================================================

/-! ## ALT Constraint

Footnote 7 of @cite{evcen-bale-barner-2026} states the alternatives constraint:

> ALT(p) ⊆ ANS(QUD) ∩ {q : Ks(q) ∨ Ks(¬q)}

The alternatives used for exhaustification must be both answers to the QUD
(contextual salience) AND propositions the speaker is competent about
(epistemic license). This is exactly what `exhaustificationLicensed` encodes
as a conjunction: `qudProvidesAlternatives qud && speakerCompetenceAssumed k`.

- Experiment 1 manipulates the first factor (QUD determines ANS)
- Experiment 3 manipulates the second factor (knowledge determines competence)
- When either factor is absent, the intersection is empty → no exhaustification
-/

/-- The ALT constraint as an intersection: alternatives are non-empty only when
both QUD provides answers and speaker is competent. `exhaustificationLicensed`
encodes this as a conjunction. -/
theorem alt_constraint_is_intersection :
    ∀ k : KnowledgeCondition, ∀ q : QUDType,
      exhaustificationLicensed k q =
      (qudProvidesAlternatives q && speakerCompetenceAssumed k) := by
  intro k q; rfl

/-- When QUD doesn't provide alternatives, exhaustification is blocked
regardless of competence — the intersection has an empty first component. -/
theorem no_qud_blocks_exhaustification :
    ∀ k : KnowledgeCondition,
      exhaustificationLicensed k .consequentFocused = false ∧
      exhaustificationLicensed k .neutral = false := by
  intro k; cases k <;> exact ⟨rfl, rfl⟩

/-- When speaker lacks competence, exhaustification is blocked regardless
of QUD — the intersection has an empty second component. -/
theorem no_competence_blocks_exhaustification :
    ∀ q : QUDType,
      exhaustificationLicensed .partialKnowledge q = false := by
  intro q; cases q <;> rfl

end EvcenBaleBarner2026
