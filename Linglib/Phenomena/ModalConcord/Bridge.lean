import Linglib.Phenomena.ModalConcord.Data
import Linglib.Fragments.English.FunctionWords
import Linglib.Core.ModalLogic
import Linglib.Core.Register
import Linglib.Theories.IntensionalSemantics.Modal.Typology

/-!
# Modal Concord Bridge — Register Approach

Connects the empirical data from Dieuleveut, Hsu & Bhatt (2025) to
the English modal fragment and modal typology infrastructure.

## Section A: Semantic equivalence

*Must* and *have to* share deontic necessity in the force-flavor space.
This is the precondition for concord: two forms that are register variants
of the same modal meaning.

## Section B: Register variants

Formalizes the register approach: *must* and *have to* are register variants
(same modal meaning, different register level). This is analogous to T/V
pronoun systems (Basque `hi`/`zu`, Japanese `boku`/`watashi`), where
forms sharing the same referential semantics differ in formality.

Register properties are derived from the fragment's `AuxEntry.register`
field and the `Core.Register.Level` type, not stipulated locally.

## Section C: Competing predictions

The register approach and the syntactic agreement approach (Zeijlstra 2007)
make different predictions about the formality of stacked modals. The data
confirms the register approach.

## Section D: Connection to modal typology

## References

* Dieuleveut, Hsu & Bhatt (2025). A Register Approach to Modal Non-Concord.
* Zeijlstra (2007). Modal concord is syntactic agreement.
* Geurts & Huitink (2006). Modal concord.
-/

namespace Phenomena.ModalConcord.Bridge

open Phenomena.ModalConcord
open Fragments.English.FunctionWords
open Core.ModalLogic (ModalForce ModalFlavor ForceFlavor)
open Core.Register (Level areVariants)
open IntensionalSemantics.Modal.Typology (satisfiesIFF satisfiesSAV)

/-! ## Section A: Semantic equivalence in the fragment -/

/-- Deontic necessity: the force-flavor pair ⟨necessity, deontic⟩. -/
private abbrev deoNec := ForceFlavor.mk .necessity .deontic

/-- *Must* expresses deontic necessity (from the English fragment). -/
theorem must_has_deontic_necessity :
    must.modalMeaning.contains deoNec = true := by native_decide

/-- *Have to* expresses deontic necessity (from the English fragment). -/
theorem haveTo_has_deontic_necessity :
    haveTo.modalMeaning.contains deoNec = true := by native_decide

/-- **Semantic overlap**: *must* and *have to* share deontic necessity.
    This shared meaning is the precondition for concord — two forms can
    only undergo concord if they express the same modal meaning. -/
theorem shared_deontic_necessity :
    must.modalMeaning.contains deoNec = true ∧
    haveTo.modalMeaning.contains deoNec = true := by
  constructor <;> native_decide

/-- *Have to* has the same deontic-circumstantial meaning as *must*
    restricted to the non-epistemic flavors. Both express necessity
    over deontic and circumstantial domains. -/
theorem haveTo_meaning_subset_of_must :
    haveTo.modalMeaning.all (must.modalMeaning.contains ·) = true := by native_decide

/-- Both *must* and *have to* satisfy IFF (Independence of Force and Flavor).
    Their meanings are Cartesian products of forces and flavors. -/
theorem both_satisfy_iff :
    satisfiesIFF must.modalMeaning = true ∧
    satisfiesIFF haveTo.modalMeaning = true := by
  constructor <;> native_decide

/-- Both satisfy SAV (Single Axis of Variability): they vary on flavor
    only, with fixed necessity force. -/
theorem both_satisfy_sav :
    satisfiesSAV must.modalMeaning = true ∧
    satisfiesSAV haveTo.modalMeaning = true := by
  constructor <;> native_decide

/-! ## Section B: Register variants

Register properties are derived directly from the fragment's `AuxEntry.register`
field, which uses `Core.Register.Level` (formal/neutral/informal). -/

/-- *Must* is marked formal in the fragment. -/
theorem must_is_formal : must.register = Level.formal := rfl

/-- *Have to* is marked informal in the fragment. -/
theorem haveTo_is_informal : haveTo.register = Level.informal := rfl

/-- **Register opposition**: *must* and *have to* are register variants —
    they differ in register level. Derived from the fragment entries. -/
theorem register_opposition : areVariants must.register haveTo.register = true := by native_decide

/-- **Register ordering**: *have to* < *must* on the formality scale
    (informal < formal). -/
theorem register_ordering : haveTo.register < must.register := by decide

/-- **Shared deontic core**: Both register variants express deontic necessity.
    Same modal meaning, different register. -/
theorem shared_deontic_core :
    must.modalMeaning.contains deoNec = true ∧
    haveTo.modalMeaning.contains deoNec = true := by
  constructor <;> native_decide

/-! ## Section C: Competing predictions

Two theories of modal concord make different predictions about the
formality of stacked modals:

**Register approach** (Dieuleveut, Hsu & Bhatt 2025):
- *Must* and *have to* are register variants of the same meaning
- Stacking creates a "split register" construction
- **Prediction**: intermediate formality (between *must* and *have to*)

**Syntactic agreement** (Zeijlstra 2007):
- One modal carries interpretable [iNec], the other uninterpretable [uNec]
- The [uNec] modal is semantically vacuous (like negative concord)
- **Prediction**: formality of stacked form = formality of single form
  (the vacuous modal contributes nothing)
-/

/-- **Register prediction confirmed**: The empirical formality rating
    of *must have to* is strictly between *must* and *have to*.
    This is the register approach's central prediction (Dieuleveut et al. §4):
    mixing a formal variant with an informal variant yields intermediate
    formality. -/
theorem register_prediction_confirmed :
    (formalityRating .haveTo).mean < (formalityRating .mustHaveTo).mean ∧
    (formalityRating .mustHaveTo).mean < (formalityRating .must).mean :=
  intermediate_formality

/-- **Syntactic agreement prediction refuted (vs must)**: If *have to*
    were semantically vacuous [uNec], *must have to* should be as formal
    as bare *must*. It is not. -/
theorem agreement_refuted_vs_must :
    (formalityRating .mustHaveTo).mean ≠ (formalityRating .must).mean := by
  native_decide

/-- **Syntactic agreement prediction refuted (vs have to)**: If *must*
    were semantically vacuous [uNec], *must have to* should be as formal
    as bare *have to*. It is not. -/
theorem agreement_refuted_vs_haveTo :
    (formalityRating .mustHaveTo).mean ≠ (formalityRating .haveTo).mean := by
  native_decide

/-- **Concord preserves modal force**: The meaning ratings for all three
    conditions are above midpoint and close to each other, confirming
    that *must have to VP* expresses single necessity (concord), not
    double necessity. If the stacked form expressed □□p, the meaning
    rating (paraphrase match with *have to*) should be much lower. -/
theorem concord_preserves_force :
    ((meaningRating .must).mean > 4 ∧
     (meaningRating .haveTo).mean > 4 ∧
     (meaningRating .mustHaveTo).mean > 4) ∧
    (meaningRating .must).mean - (meaningRating .mustHaveTo).mean < 1/2 :=
  ⟨meaning_above_midpoint, meaning_must_close_to_mustHaveTo⟩

/-! ## Section D: Connection to modal typology

Modal concord only arises between forms with overlapping force-flavor
meanings. The IFF universal (Steinert-Threlkeld, Imel & Guo 2023)
predicts that natural-language modals have Cartesian-product meanings.
Since Cartesian products with the same force axis share all force-flavor
pairs, IFF-satisfying necessity modals are natural concord candidates. -/

/-- The deontic necessity overlap between *must* and *have to* is
    non-accidental: both are IFF-satisfying necessity modals. Any two
    IFF modals with singleton force {necessity} and overlapping flavor
    sets share deontic necessity whenever both express it. -/
theorem iff_enables_concord :
    satisfiesIFF must.modalMeaning = true ∧
    satisfiesIFF haveTo.modalMeaning = true ∧
    must.modalMeaning.contains deoNec = true ∧
    haveTo.modalMeaning.contains deoNec = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end Phenomena.ModalConcord.Bridge
