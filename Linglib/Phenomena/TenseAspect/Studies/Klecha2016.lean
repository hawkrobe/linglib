import Linglib.Theories.Semantics.Tense.ModalTense
import Linglib.Theories.Semantics.Modality.TemporalConstraint
import Linglib.Fragments.English.Predicates.Verbal

/-!
# @cite{klecha-2016}: Modality and Embedded Temporal Operators

Klecha's central result: the temporal orientation of embedded clauses under
attitude verbs is determined by the **modal base pronoun** (DOX vs. CIR),
not by the modal or attitude verb per se.

## Empirical puzzle

Under past-tense *think* (doxastic), embedded tense cannot be future-oriented:
- "Martina thought Carissa got pregnant" → RT ≤ thinking time

Under past-tense *hope* (preferential / CIR-compatible), embedded tense
can be future-oriented:
- "Martina hoped Carissa got pregnant" → RT > hoping time (CIR reading)

## Theoretical mechanism

1. DOX returns *actual histories* ending at the eval time → RT ≤ EvalT
   (Upper Limit Constraint derived from DOX's temporal character)
2. CIR returns *future histories* departing from the eval time → RT > EvalT
   (future orientation permitted)
3. Embedded tense (PAST or NPST) composes with the modal base constraint.
   The intersection determines what temporal orientations are available:
   DOX ∧ PAST = past; DOX ∧ NPST = simultaneous; CIR ∧ NPST = future;
   CIR ∧ PAST = impossible.

## What this file verifies

- Attitude verb classifications from `Fragments.English` derive the correct
  modal base compatibility
- *think*/*believe* are DOX-only (block future)
- *hope*/*pray* permit CIR (allow future)
- The Upper Limit Constraint follows from doxastic temporal character
- Hacquard's positional analysis is complementary: position determines
  WHAT time; modal base kind determines WHICH DIRECTION
- Table 1 modal-temporal correspondence via `ModalFlavor.toModalBaseKind`
- NPST is strictly weaker than present (key to the analysis)
- Hope ambiguity: DOX → past, CIR → future

-/

namespace Klecha2016

open Core.Verbs (Attitude Preferential Veridicality)
open Core.Modality (ModalBaseKind)
open Semantics.Modality.TemporalConstraint (attitudeTemporalConstraint
  doxConstrainsRT cirConstrainsRT Attitude.toModalBaseKind
  dox_compatible_with_past dox_incompatible_with_future cir_compatible_with_future
  permitsCirc_iff_cir ModalFlavor.toModalBaseKind
  epistemic_blocks_future circumstantial_permits_future deontic_permits_future
  non_epistemic_is_cir)
open Fragments.English.Predicates.Verbal (think believe hope pray)
open Semantics.Tense.ModalTense (embeddedRTConstraint think_blocks_future
  think_permits_past hope_permits_future hope_permits_past
  dox_past_iff dox_npst_iff cir_npst_iff cir_past_impossible)
open Core.Tense (GramTense)
open Core.Modality (ModalFlavor)


-- ════════════════════════════════════════════════════════════════
-- § 1. Attitude verb modal base classification
-- ════════════════════════════════════════════════════════════════

/-- *think* is classified as doxastic → DOX only. -/
theorem think_is_doxastic :
    think.attitude = some (.doxastic .nonVeridical) := rfl

/-- *believe* is classified as doxastic → DOX only. -/
theorem believe_is_doxastic :
    believe.attitude = some (.doxastic .nonVeridical) := rfl

/-- *hope* is classified as preferential → can take CIR. -/
theorem hope_is_preferential :
    hope.attitude = some (.preferential (.degreeComparison .positive)) := rfl

/-- *pray* is classified as preferential → can take CIR. -/
theorem pray_is_preferential :
    pray.attitude = some (.preferential (.degreeComparison .positive)) := rfl


-- ════════════════════════════════════════════════════════════════
-- § 2. Derived modal base compatibility
-- ════════════════════════════════════════════════════════════════

/-- *think*'s attitude blocks circumstantial modal base. -/
theorem think_blocks_cir :
    (Attitude.doxastic .nonVeridical).permitsCircumstantial = false := rfl

/-- *believe*'s attitude blocks circumstantial modal base. -/
theorem believe_blocks_cir :
    (Attitude.doxastic .nonVeridical).permitsCircumstantial = false := rfl

/-- *hope*'s attitude permits circumstantial modal base. -/
theorem hope_permits_cir :
    (Attitude.preferential (.degreeComparison .positive)).permitsCircumstantial = true := rfl

/-- *pray*'s attitude permits circumstantial modal base. -/
theorem pray_permits_cir :
    (Attitude.preferential (.degreeComparison .positive)).permitsCircumstantial = true := rfl


-- ════════════════════════════════════════════════════════════════
-- § 3. Modal base kind derivation
-- ════════════════════════════════════════════════════════════════

/-- *think*'s derived modal base kind is doxastic. -/
theorem think_modal_base :
    Attitude.toModalBaseKind (.doxastic .nonVeridical) = ModalBaseKind.doxastic := rfl

/-- *hope*'s derived modal base kind is circumstantial. -/
theorem hope_modal_base :
    Attitude.toModalBaseKind (.preferential (.degreeComparison .positive)) =
    ModalBaseKind.circumstantial := rfl


-- ════════════════════════════════════════════════════════════════
-- § 4. Temporal orientation predictions
-- ════════════════════════════════════════════════════════════════

/-! ### "Martina thought Carissa got pregnant"

Under *think* (DOX), the embedded past tense is genuine past: RT < thinking time.
Future-oriented readings are blocked. -/

/-- Past reading under *think* is compatible. -/
theorem thought_pregnant_past (thinkTime embRT : ℤ) (h : embRT < thinkTime) :
    embeddedRTConstraint .doxastic thinkTime embRT :=
  think_permits_past thinkTime embRT h

/-- Future reading under *think* is blocked. -/
theorem thought_pregnant_no_future (thinkTime embRT : ℤ) (h : embRT > thinkTime) :
    ¬ embeddedRTConstraint .doxastic thinkTime embRT :=
  think_blocks_future thinkTime embRT h


/-! ### "Martina hoped Carissa got pregnant"

Under *hope* (CIR), the "past" morphology on "got" is SOT agreement —
the embedded tense can be future-oriented: RT > hoping time.

But *hope* can also take DOX, giving a past-oriented reading:
"Martina hoped Carissa got pregnant" → RT < hoping time (DOX). -/

/-- Future reading under *hope* is permitted (via CIR). -/
theorem hoped_pregnant_future (hopeTime embRT : ℤ) (h : embRT > hopeTime) :
    embeddedRTConstraint .circumstantial hopeTime embRT :=
  hope_permits_future hopeTime embRT h

/-- Past reading under *hope* is also permitted (via DOX). -/
theorem hoped_pregnant_past (hopeTime embRT : ℤ) (h : embRT < hopeTime) :
    embeddedRTConstraint .doxastic hopeTime embRT :=
  hope_permits_past hopeTime embRT h


-- ════════════════════════════════════════════════════════════════
-- § 5. The Upper Limit Constraint is DERIVED
-- ════════════════════════════════════════════════════════════════

/-- The ULC is not a stipulated constraint — it follows from DOX's
    temporal character. Any doxastic attitude verb imposes RT ≤ EvalT,
    blocking future orientation. -/
theorem ulc_derived_from_dox (evalTime refTime : ℤ) :
    attitudeTemporalConstraint .doxastic evalTime refTime ↔
    refTime ≤ evalTime :=
  Iff.rfl

/-- The CIR temporal constraint is the complement: RT > EvalT. -/
theorem cir_is_future (evalTime refTime : ℤ) :
    attitudeTemporalConstraint .circumstantial evalTime refTime ↔
    refTime > evalTime :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § 6. Compositional intersection: tense × modal base
-- ════════════════════════════════════════════════════════════════

/-! The central compositional predictions. Each cell in the 2×2
matrix (DOX/CIR × PAST/NPST) has a determinate temporal orientation.
These theorems instantiate the general results from `ModalTense` at ℤ. -/

/-- DOX + PAST = past: "Martina thought Carissa got pregnant" (genuine
    past reading). RT < thinking time. -/
theorem dox_past_gives_past (t r : ℤ) :
    embeddedRTConstraint .doxastic t r ∧ GramTense.constrains .past r t ↔
    r < t :=
  dox_past_iff t r

/-- DOX + NPST = simultaneous: "Martina thought Carissa was pregnant"
    where "was" = SOT agreement over NPST. RT = thinking time. -/
theorem dox_npst_gives_simultaneous (t r : ℤ) :
    embeddedRTConstraint .doxastic t r ∧ GramTense.constrains .nonpast r t ↔
    r = t :=
  dox_npst_iff t r

/-- CIR + NPST = future: "Martina hoped Carissa got pregnant" where
    "got" = SOT agreement over NPST + CIR. RT > hoping time. -/
theorem cir_npst_gives_future (t r : ℤ) :
    embeddedRTConstraint .circumstantial t r ∧ GramTense.constrains .nonpast r t ↔
    r > t :=
  cir_npst_iff t r

/-- CIR + PAST = impossible: no RT can be both > t (CIR) and < t (PAST). -/
theorem cir_past_is_impossible (t r : ℤ) :
    ¬(embeddedRTConstraint .circumstantial t r ∧ GramTense.constrains .past r t) :=
  cir_past_impossible t r


-- ════════════════════════════════════════════════════════════════
-- § 7. NPST is not Present
-- ════════════════════════════════════════════════════════════════

/-! A key theoretical innovation: NPST (u ≤ t, i.e., ref ≥ perspective) is
strictly weaker than present (ref = perspective). This matters because NPST
includes future-oriented readings that present would exclude. -/

/-- Present entails nonpast: if ref = persp, then ref ≥ persp. -/
theorem present_implies_nonpast (r p : ℤ) (h : GramTense.constrains .present r p) :
    GramTense.constrains .nonpast r p :=
  ge_of_eq h

/-- Nonpast does not entail present: there exist r, p where ref ≥ persp
    but ref ≠ persp (namely, any future time). -/
theorem nonpast_strictly_weaker :
    ∃ r p : ℤ, GramTense.constrains .nonpast r p ∧
              ¬ GramTense.constrains .present r p := by
  exact ⟨1, 0, by simp [GramTense.constrains],
                by simp [GramTense.constrains]⟩


-- ════════════════════════════════════════════════════════════════
-- § 8. Table 1: Modal flavor → temporal orientation
-- ════════════════════════════════════════════════════════════════

/-! @cite{klecha-2016} Table 1 shows that epistemic modals
("She has to be home by now") are past/present-oriented, while
circumstantial/deontic/bouletic modals ("She has to be home tomorrow")
are future-oriented. This follows from `ModalFlavor.toModalBaseKind`. -/

/-- Epistemic "have to" blocks future orientation. -/
theorem epistemic_haveto_no_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .epistemic) .future = false :=
  epistemic_blocks_future

/-- Circumstantial "have to" permits future orientation. -/
theorem circumstantial_haveto_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .circumstantial) .future = true :=
  circumstantial_permits_future

/-- Deontic "have to" permits future orientation. -/
theorem deontic_haveto_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .deontic) .future = true :=
  deontic_permits_future

/-- Bouletic modals permit future orientation. -/
theorem bouletic_modal_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .bouletic) .future = true := rfl

/-- All non-epistemic flavors are CIR-like. -/
theorem non_epistemic_all_cir (f : ModalFlavor) (h : f ≠ .epistemic) :
    ModalFlavor.toModalBaseKind f = ModalBaseKind.circumstantial :=
  non_epistemic_is_cir f h


-- ════════════════════════════════════════════════════════════════
-- § 9. Reportatives pattern with doxastics
-- ════════════════════════════════════════════════════════════════

/-! @cite{klecha-2016} (80): "*I told John that it rains tomorrow"
is unacceptable — *tell* imposes an upper limit, patterning with
doxastic verbs. Reportatives use DOX, blocking future orientation. -/

/-- Reportatives (tell, say) impose the upper limit like doxastics:
    the future reading is blocked. -/
theorem reportative_blocks_future (tellTime embRT : ℤ) (h : embRT > tellTime) :
    ¬ embeddedRTConstraint .doxastic tellTime embRT :=
  think_blocks_future tellTime embRT h


-- ════════════════════════════════════════════════════════════════
-- § 10. Classification table
-- ════════════════════════════════════════════════════════════════

/-- Klecha's classification: attitude verbs and their temporal orientation
    predictions, derived from `Attitude.permitsCircumstantial`. -/
structure AttitudeOrientationDatum where
  verb : String
  isDoxOnly : Bool
  permitsULC : Bool     -- RT ≤ EvalT (always true for all verbs)
  permitsFuture : Bool  -- RT > EvalT (only when CIR available)
  deriving Repr, DecidableEq

def thinkDatum : AttitudeOrientationDatum :=
  { verb := "think", isDoxOnly := true, permitsULC := true, permitsFuture := false }

def believeDatum : AttitudeOrientationDatum :=
  { verb := "believe", isDoxOnly := true, permitsULC := true, permitsFuture := false }

def hopeDatum : AttitudeOrientationDatum :=
  { verb := "hope", isDoxOnly := false, permitsULC := true, permitsFuture := true }

def prayDatum : AttitudeOrientationDatum :=
  { verb := "pray", isDoxOnly := false, permitsULC := true, permitsFuture := true }

def classificationTable : List AttitudeOrientationDatum :=
  [thinkDatum, believeDatum, hopeDatum, prayDatum]

/-- DOX-only verbs all block future orientation. -/
theorem dox_only_block_future :
    (classificationTable.filter (·.isDoxOnly)).all (·.permitsFuture == false) = true := by
  decide

/-- CIR-compatible verbs all permit future orientation. -/
theorem cir_compat_permit_future :
    (classificationTable.filter (! ·.isDoxOnly)).all (·.permitsFuture) = true := by
  decide


end Klecha2016
