import Linglib.Phenomena.Conditionals.Studies.EvcenBaleBarner2026.Data
import Linglib.Theories.Semantics.Conditionals.Exhaustivity
import Linglib.Theories.Semantics.Conditionals.Basic
import Linglib.Theories.Pragmatics.NeoGricean.Core.Competence

/-!
# @cite{evcen-bale-barner-2026} — Bridge
@cite{von-fintel-2001} @cite{horn-2000} @cite{cornulier-1983}

Connects the experimental findings of @cite{evcen-bale-barner-2026} to the
answer-level exhaustification theory of conditional perfection.

## Full Argument Chain

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

## Dependency Chain

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

namespace Phenomena.Conditionals.Studies.EvcenBaleBarner2026.Bridge

open Semantics.Conditionals
open Semantics.Conditionals.Exhaustivity
open Core.Proposition

private theorem Bool.of_not_eq_true {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b <;> simp_all

-- ============================================================================
-- Section A: 3-Button Experimental Scenario
-- ============================================================================

/-- Triggers in the experimental paradigm: three buttons. -/
inductive Button3Trigger where
  | A | B | C
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

instance : Fintype Button3World where
  elems := {.pressA_plays, .pressA_silent, .pressB_plays,
            .pressB_silent, .pressC_plays, .pressC_silent}
  complete := fun x => by cases x <;> simp

/-- Button A is pressed. -/
def pressA : BProp Button3World
  | .pressA_plays | .pressA_silent => true
  | _ => false

/-- The target sound plays. -/
def soundPlays : BProp Button3World
  | .pressA_plays | .pressB_plays | .pressC_plays => true
  | _ => false

/-- Button A causes the target sound. -/
def aCausesSound : BProp Button3World
  | .pressA_plays => true | _ => false

/-- Button B causes the target sound. -/
def bCausesSound : BProp Button3World
  | .pressB_plays => true | _ => false

/-- Button C causes the target sound. -/
def cCausesSound : BProp Button3World
  | .pressC_plays => true | _ => false

/-- The answer space for the 3-button experimental paradigm.

Maps the scenario into the `AnswerSpace` structure: three triggers (buttons),
each with a causal relation to the target sound. -/
def button3AnswerSpace : AnswerSpace Button3Trigger Button3World :=
  { causes := fun t w => match t with
      | .A => aCausesSound w = true
      | .B => bCausesSound w = true
      | .C => cCausesSound w = true
    triggers := {.A, .B, .C} }

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
    (h_exh : exhaustifiedAnswer button3AnswerSpace .A w)
    (h_coverage : soundPlays w = true →
      ∃ t' ∈ button3AnswerSpace.triggers, button3AnswerSpace.causes t' w)
    (hnp : pressA w = false) : soundPlays w = false := by
  -- Step 1: Trigger A requires pressing A
  have h_trp : ∀ w', button3AnswerSpace.causes .A w' → pressA w' = true := by
    intro w' h; cases w' <;> simp_all [button3AnswerSpace, aCausesSound, pressA]
  -- Step 2: All alternative triggers are IE (via general lemma)
  have h_ie : ∀ t' ∈ button3AnswerSpace.triggers, t' ≠ .A →
      NeoGricean.Exhaustivity.isInnocentlyExcludable
        (answerAlternatives button3AnswerSpace .A)
        (answerProp button3AnswerSpace .A)
        (answerProp button3AnswerSpace t') := by
    intro t' _ht' hne
    -- Apply the general IE lemma: all alternatives are IE when full exclusion
    -- is consistent. Witness: pressA_plays (A causes, B and C do not).
    apply all_alt_innocently_excludable
    · -- Consistency: ∃ w, φ w ∧ ∀ a ∈ ALT, ¬(a w)
      refine ⟨.pressA_plays, rfl, ?_⟩
      intro a ⟨t'', ht''_mem, ht''_ne, ht''_eq⟩
      cases t'' with
      | A => exact absurd rfl ht''_ne
      | B => subst ht''_eq; simp [answerProp, button3AnswerSpace, bCausesSound]
      | C => subst ht''_eq; simp [answerProp, button3AnswerSpace, cCausesSound]
    · -- t' ∈ ALT
      cases t' with
      | A => exact absurd rfl hne
      | B => exact ⟨.B, Or.inr (Or.inl rfl), Button3Trigger.noConfusion, rfl⟩
      | C => exact ⟨.C, Or.inr (Or.inr rfl), Button3Trigger.noConfusion, rfl⟩
  -- Step 3: ¬(pressA w = true)
  have h_not_p : ¬(pressA w = true) := by simp [hnp]
  -- Step 4: Apply the theory chain
  have h_not_sound : ¬(soundPlays w = true) :=
    exhaustification_yields_perfection button3AnswerSpace .A
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
def vonFintelPrediction {Trigger W : Type*}
    (as : AnswerSpace Trigger W) (t : Trigger) (w : W) : Prop :=
  ∀ t' ∈ as.triggers, t' ≠ t → ¬as.causes t' w

/-- What @cite{horn-2000}'s account predicts: some non-asserted trigger is
excluded, but we don't know which (existential, unspecified). -/
def hornPrediction {Trigger W : Type*}
    (as : AnswerSpace Trigger W) (t : Trigger) (w : W) : Prop :=
  ∃ t' ∈ as.triggers, t' ≠ t ∧ ¬as.causes t' w

/-- **Von Fintel entails Horn**: per-trigger exclusion implies existential exclusion.

If we know that every specific alternative trigger is excluded (von Fintel),
then certainly some trigger is excluded (Horn). -/
theorem vonFintel_entails_horn
    {Trigger W : Type*} (as : AnswerSpace Trigger W) (t : Trigger) (w : W)
    (h_other : ∃ t' ∈ as.triggers, t' ≠ t)
    (h_vf : vonFintelPrediction as t w) : hornPrediction as t w := by
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
      hornPrediction button3AnswerSpace .A w ∧
      ¬vonFintelPrediction button3AnswerSpace .A w := by
  -- At pressB_plays: B causes sound (✓), C doesn't (✓)
  -- Horn: ∃ t'≠A, ¬causes t' → C. ✓
  -- von Fintel: ∀ t'≠A, ¬causes t' → B causes sound. ✗
  refine ⟨.pressB_plays, ?_, ?_⟩
  · exact ⟨.C, Or.inr (Or.inr rfl), Button3Trigger.noConfusion,
      by simp [button3AnswerSpace, cCausesSound]⟩
  · intro h
    have := h .B (Or.inr (Or.inl rfl)) Button3Trigger.noConfusion
    simp [button3AnswerSpace, bCausesSound] at this

/-- **Von Fintel is strictly stronger than Horn.**

Combining the two: von Fintel's per-trigger alternatives generate strictly
stronger predictions than Horn's unconditional alternative. The 3-button
paradigm discriminates between the two accounts. -/
theorem vonFintel_strictly_stronger_than_horn :
    -- von Fintel → Horn (forward direction)
    (∀ w : Button3World, vonFintelPrediction button3AnswerSpace .A w →
      hornPrediction button3AnswerSpace .A w) ∧
    -- Horn ↛ von Fintel (backward direction fails)
    (∃ w : Button3World, hornPrediction button3AnswerSpace .A w ∧
      ¬vonFintelPrediction button3AnswerSpace .A w) := by
  constructor
  · intro w h
    exact vonFintel_entails_horn button3AnswerSpace .A w
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

1. **Formal**: `perfection_not_entailed` proves the biconditional is not
   semantically entailed by the material conditional.

2. **Experimental**: Perfection rates vary with QUD type and speaker knowledge.
   Semantic entailments are invariant across these factors. -/
theorem cp_is_pragmatic :
    (∃ (W : Type) (p q : Prop' W) (w : W),
      materialImp p q w ∧ ¬(conditionalPerfection p q w)) ∧
    (exp1Data .antecedentFocused).perfectionRate ≠
    (exp1Data .consequentFocused).perfectionRate ∧
    (exp3Data .fullKnowledge).perfectionRate ≠
    (exp3Data .partialKnowledge).perfectionRate := by
  exact ⟨perfection_not_entailed, by native_decide, by native_decide⟩

end Phenomena.Conditionals.Studies.EvcenBaleBarner2026.Bridge
