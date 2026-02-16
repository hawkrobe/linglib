import Linglib.Phenomena.Lakoff1970.Data
import Linglib.Fragments.English.Tense
import Linglib.Theories.Semantics.Tense.Perspective

/-!
# Lakoff (1970) Bridge Theorems

Connects the empirical judgments in `Data.lean` to theoretical predictions
from `Perspective.lean` (Lakoff predicates) and `Fragments/English/Tense.lean`
(perspective entries with form types).

## Structure

1. **Per-datum form-type verification**: each judgment's `formType` matches
   the corresponding Fragment entry's `formType`.
2. **False-tense diagnostic**: false tense + periphrastic → unacceptable,
   derived from `falseTenseRequiresSynthetic`.
3. **Temporal-perspective bridges**: false-past data satisfies `eventTime = speechTime`.
4. **Novel-info and salience bridges**: connect §2 and §4 data to predicates.

## References

- Lakoff, R. (1970). Tense and its relation to participants. *Language* 46(4).
-/

namespace Phenomena.Lakoff1970.Bridge

open Phenomena.Lakoff1970.Data
open Fragments.English.Tense
open TruthConditional.Sentence.Tense.Perspective
open TruthConditional.Sentence.Tense
open Core.Morphology.Tense

-- ════════════════════════════════════════════════════
-- § 1. Per-Datum Form Type Verification
-- ════════════════════════════════════════════════════

/-- ex4a (false past, synthetic) matches simplePastPerspective's form type. -/
theorem ex4a_formType :
    ex4a.formType = simplePastPerspective.formType := rfl

/-- ex8a (false past, periphrastic) matches usedTo's form type. -/
theorem ex8a_formType :
    ex8a.formType = usedTo.formType := rfl

/-- ex9a (true past, periphrastic) matches usedTo's form type. -/
theorem ex9a_formType :
    ex9a.formType = usedTo.formType := rfl

-- ════════════════════════════════════════════════════
-- § 2. False-Tense Diagnostic
-- ════════════════════════════════════════════════════

/-- Synthetic forms pass the false-tense diagnostic. Matches ex4a (grammatical). -/
theorem synthetic_allows_false_tense :
    falseTenseRequiresSynthetic .falseTense .synthetic = true := rfl

/-- Periphrastic forms fail the false-tense diagnostic. Matches ex8a (ungrammatical). -/
theorem periphrastic_blocks_false_tense :
    falseTenseRequiresSynthetic .falseTense .periphrastic = false := rfl

/-- True tense passes with any form type — periphrastic is fine. Matches ex9a. -/
theorem true_tense_any_form :
    falseTenseRequiresSynthetic .trueTense .periphrastic = true := rfl

/-- The Fragment entry for "used to" correctly blocks false tense. -/
theorem usedTo_entry_blocks_false :
    usedTo.allowsFalseTense = false := rfl

/-- The Fragment entry for simple past correctly allows false tense. -/
theorem simplePast_entry_allows_false :
    simplePastPerspective.allowsFalseTense = true := rfl

-- ════════════════════════════════════════════════════
-- § 3. False Past Satisfies Temporal Present
-- ════════════════════════════════════════════════════

/-- When `falsePast` holds, the event IS at speech time (T = S), matching
    the UP present constraint. The past surface tense is purely psychological.
    This connects Lakoff's false-past data (ex4a) to the Reichenbach frame. -/
theorem false_past_is_temporally_present (f : TensePerspective ℤ)
    (h : falsePast f) :
    f.eventTime = f.speechTime :=
  h.1

/-- Under `falsePast`, `classifyUse .past` returns `.falseTense`. -/
theorem false_past_classified_correctly (f : TensePerspective ℤ)
    (h : falsePast f) :
    classifyUse .past f = TenseUse.falseTense := by
  simp only [classifyUse]
  have h_eq := h.1
  split
  · omega
  · rfl

-- ════════════════════════════════════════════════════
-- § 4. Novel-Information Present (§2)
-- ════════════════════════════════════════════════════

/-- When `novelInfoPresent` holds, the event is at speech time AND the content
    is new to the hearer. This licenses present tense under a past matrix verb.
    Connects to ex13b. -/
theorem novel_info_licenses_present (f : TensePerspective ℤ)
    (h : novelInfoPresent f) :
    f.hearerNovelty = true ∧ f.eventTime = f.speechTime :=
  ⟨h.1, h.2⟩

-- ════════════════════════════════════════════════════
-- § 5. Perfect Requires Salience (§4)
-- ════════════════════════════════════════════════════

/-- When `perfectRequiresSalience` holds, the speaker finds the event currently
    relevant. This licenses present perfect (ex22a: "Shakespeare has written...").
    When it fails, present perfect is infelicitous (ex22b: *"Shakespeare has
    quarreled..."). -/
theorem perfect_salience_required (f : TensePerspective ℤ)
    (h : perfectRequiresSalience f) :
    f.speakerSalience = true :=
  h

-- ════════════════════════════════════════════════════
-- § 6. Will-Deletion (§5)
-- ════════════════════════════════════════════════════

/-- When `willDeletion` holds, the event is future (S < T) but salient,
    licensing present-for-future ("John dies tomorrow" = ex27b).
    When salience fails ("It rains Thursday" = ex25b), will-deletion is blocked. -/
theorem will_deletion_requires_future_and_salience (f : TensePerspective ℤ)
    (h : willDeletion f) :
    f.speechTime < f.eventTime ∧ f.speakerSalience = true :=
  ⟨h.1, h.2⟩

-- ════════════════════════════════════════════════════
-- § 7. Cross-Cutting: Acceptability Predictions
-- ════════════════════════════════════════════════════

/-- All grammatical false-tense examples have synthetic form type. -/
theorem grammatical_false_tense_all_synthetic :
    (falseTenseJudgments.filter
      (λ j => j.acceptability == .grammatical)).all
      (λ j => j.formType == .synthetic) = true := rfl

/-- The sole false-tense-with-periphrastic judgment is ungrammatical. -/
theorem false_periphrastic_is_ungrammatical :
    (ex8a.tenseUse == .falseTense &&
     ex8a.formType == .periphrastic &&
     ex8a.acceptability == .ungrammatical) = true := rfl

end Phenomena.Lakoff1970.Bridge
