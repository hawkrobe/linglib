import Linglib.Phenomena.Conditionals.Studies.EvcenBaleBarner2026.Data
import Linglib.Theories.Semantics.Conditionals.Exhaustivity
import Linglib.Theories.Semantics.Conditionals.Basic

/-!
# Evcen, Bale & Barner (2026) — Bridge @cite{evcen-bale-barner-2026}

Connects the experimental findings of Evcen, Bale & Barner (2026) to the
answer-level exhaustification theory of conditional perfection (von Fintel 2001)
as formalized in `Semantics.Conditionals.Exhaustivity`.

## Dependency Chain

The theory makes a directional prediction through the following chain:

```
exhaustifiedAnswer_excludes         (exhIE → local exclusion for IE alternatives)
    ↓
exhaustification_yields_perfection  (exhIE + all alts IE + coverage → perfection)
    ↓
theory_chain_button_perfection      (chain instantiated for the experimental scenario)
    ↓
coverage_without_exclusion_insufficient  (without exclusion → perfection fails)
    ↓
Prediction: perfection iff exclusion is available
    ↓
antecedent_focus_highest            (data confirms: QUDs providing exclusion > those without)
```

The theory predicts an asymmetry: perfection when exhaustification provides
exclusion (antecedent-focus QUD, knowledgeable speaker), no perfection when
exclusion is unavailable (consequent-focus QUD, ignorant speaker). The
experimental data confirm exactly this pattern.
-/

namespace Phenomena.Conditionals.Studies.EvcenBaleBarner2026.Bridge

open Semantics.Conditionals
open Semantics.Conditionals.Exhaustivity
open Core.Proposition

private theorem Bool.of_not_eq_true {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b <;> simp_all

-- ============================================================================
-- Section A: Experimental Scenario
-- ============================================================================

/-- Triggers in the experimental paradigm: two buttons. -/
inductive Button2Trigger where
  | A | B
  deriving DecidableEq, BEq, Repr

/-- The 4 possible worlds in a 2-button scenario. -/
inductive Button2World where
  | pressA_plays
  | pressA_silent
  | pressB_plays
  | pressB_silent
  deriving DecidableEq, BEq, Repr

instance : Fintype Button2World where
  elems := {.pressA_plays, .pressA_silent, .pressB_plays, .pressB_silent}
  complete := fun x => by cases x <;> simp

/-- Button A is pressed. -/
def pressA : BProp Button2World
  | .pressA_plays => true | .pressA_silent => true | _ => false

/-- Music plays. -/
def musicPlays : BProp Button2World
  | .pressA_plays => true | .pressB_plays => true | _ => false

/-- Button A causes music (at this world). -/
def aCausesMusic : BProp Button2World
  | .pressA_plays => true | _ => false

/-- Button B causes music (at this world). -/
def bCausesMusic : BProp Button2World
  | .pressB_plays => true | _ => false

/-- The answer space for the experimental paradigm.

Maps the 2-button scenario into the `AnswerSpace` structure from the
exhaustification theory, with boolean causation lifted to `Prop`. -/
def buttonAnswerSpace : AnswerSpace Button2Trigger Button2World :=
  { causes := fun t w => match t with
      | .A => aCausesMusic w = true
      | .B => bCausesMusic w = true
    triggers := {.A, .B} }

-- ============================================================================
-- Section B: Theory Chain Applied to Scenario
-- ============================================================================

/-- **Theory chain: exhaustification yields perfection in the button scenario.**

This instantiates `exhaustification_yields_perfection` for the experimental
paradigm. The theorem says: if the exhaustified answer holds at `w`
(triggered by antecedent-focus QUD) and all alternative triggers are
innocently excludable (licensed by speaker knowledge), then ¬pressA → ¬music.

The hypotheses map to experimental conditions:
- `h_exh`: exhaustified answer holds (antecedent-focus QUD triggers EXH)
- `h_coverage`: every music event has a button cause (closed domain)
- `hnp`: button A is not pressed

The IE condition is discharged by `singleton_alt_innocently_excludable`:
in the 2-button scenario, ALT = {answerProp .B} is a singleton, and the
witness `pressA_plays` establishes joint consistency of φ ∧ ∼a. -/
theorem theory_chain_button_perfection
    (w : Button2World)
    (h_exh : exhaustifiedAnswer buttonAnswerSpace .A w)
    (h_coverage : musicPlays w = true →
      ∃ t' ∈ buttonAnswerSpace.triggers, buttonAnswerSpace.causes t' w)
    (hnp : pressA w = false) : musicPlays w = false := by
  -- Step 1: Prepare hypotheses for the theory chain
  -- h_t_requires_p: if trigger A fires at w', button A was pressed at w'
  have h_trp : ∀ w', buttonAnswerSpace.causes .A w' → pressA w' = true := by
    intro w' h; cases w' <;> simp_all [buttonAnswerSpace, aCausesMusic, pressA]
  -- h_all_ie: all alternative triggers are IE
  -- In the 2-button scenario, the only alternative to A is B (singleton ALT).
  -- By singleton_alt_innocently_excludable, B is IE given the witness pressA_plays.
  have h_ie : ∀ t' ∈ buttonAnswerSpace.triggers, t' ≠ .A →
      NeoGricean.Exhaustivity.isInnocentlyExcludable
        (answerAlternatives buttonAnswerSpace .A)
        (answerProp buttonAnswerSpace .A)
        (answerProp buttonAnswerSpace t') := by
    intro t' _ht' hne
    -- t' ∈ {.A, .B} and t' ≠ .A, so t' = .B
    cases t' with
    | A => exact absurd rfl hne
    | B =>
      apply singleton_alt_innocently_excludable
      -- h_mem: answerProp .B ∈ answerAlternatives .A
      · exact ⟨.B, Or.inr rfl, Button2Trigger.noConfusion, rfl⟩
      -- h_all_eq: all alternatives equal answerProp .B
      · intro a' ⟨t'', ht''_mem, ht''_ne, ht''_eq⟩
        cases t'' with
        | A => exact absurd rfl ht''_ne
        | B => exact ht''_eq
      -- h_consist: ∃ w, (answerProp .A) w ∧ ¬((answerProp .B) w)
      · exact ⟨.pressA_plays, rfl, by simp [answerProp, buttonAnswerSpace, bCausesMusic]⟩
  -- h_not_p: ¬(pressA w = true)
  have h_not_p : ¬(pressA w = true) := by simp [hnp]
  -- Step 2: Apply the theory chain
  -- exhaustifiedAnswer → exclusion (via IE) → perfection (with coverage)
  have h_not_music : ¬(musicPlays w = true) :=
    exhaustification_yields_perfection buttonAnswerSpace .A
      (fun w => pressA w = true) (fun w => musicPlays w = true) w
      h_trp h_ie h_coverage h_exh h_not_p
  -- Step 3: Convert ¬(musicPlays w = true) to musicPlays w = false
  exact Bool.of_not_eq_true h_not_music

-- ============================================================================
-- Section C: Direct Verification (Agrees with Theory Chain)
-- ============================================================================

/-- **Direct verification: exclusion + ¬pressA → ¬music.**

Verified by exhaustive case analysis on the 4-world type. This serves as
a sanity check: the result of the theory chain (Section B) agrees with
brute-force verification. -/
theorem two_button_perfection :
    ∀ w : Button2World,
      bCausesMusic w = false → pressA w = false → musicPlays w = false := by
  native_decide

-- ============================================================================
-- Section D: Theory Predicts Asymmetry
-- ============================================================================

/-- **Without exclusion, perfection fails.**

Coverage alone (every C-event has some trigger) does NOT yield ¬p → ¬C.
Witness: a 2-trigger scenario where trigger t requires p but trigger t' fires
at ¬p-worlds. Coverage holds, but ¬p ∧ C.

This is the other half of the theory's prediction: perfection requires
exclusion (from exhaustification), not just coverage. Without exclusion
(e.g., under consequent-focus QUD or ignorant speaker), the theory predicts
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
-- Section E: Data Confirms the Predicted Asymmetry
-- ============================================================================

/-- **Data confirms: antecedent-focus QUD promotes perfection.**

The theory predicts higher perfection under antecedent-focus QUDs (which
trigger exhaustification and hence exclusion) than under consequent-focus
QUDs or no QUD (which don't). Experiment 1 confirms both orderings. -/
theorem antecedent_focus_highest :
    exp1_antecedentFocus.perfectionRate > exp1_consequentFocus.perfectionRate ∧
    exp1_antecedentFocus.perfectionRate > exp1_noQUD.perfectionRate := by
  constructor <;> native_decide

/-- **Data confirms: speaker knowledge promotes perfection.**

The theory predicts higher perfection when the speaker is knowledgeable
(licensing the assumption that unmentioned alternatives are false, hence
exclusion) than when ignorant (no exclusion license). Experiment 3 confirms. -/
theorem knowledge_promotes_perfection :
    exp3_knowledgeable.perfectionRate > exp3_ignorant.perfectionRate := by
  native_decide

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
    exp1_antecedentFocus.perfectionRate ≠ exp1_consequentFocus.perfectionRate ∧
    exp3_knowledgeable.perfectionRate ≠ exp3_ignorant.perfectionRate := by
  exact ⟨perfection_not_entailed, by native_decide, by native_decide⟩

end Phenomena.Conditionals.Studies.EvcenBaleBarner2026.Bridge
