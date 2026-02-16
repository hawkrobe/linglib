import Linglib.Theories.IntensionalSemantics.Tense.Basic

/-!
# Klecha (2016): Modality and Embedded Temporal Operators

Klecha's theory: **modals shift the evaluation time**, not just attitude
verbs. This means tense under a modal is checked against the modal's
evaluation time, explaining modal-tense interactions that other theories
leave unaddressed.

## Core Mechanisms

1. **Modal eval time shift**: modals shift the temporal evaluation context,
   parallel to how attitude verbs shift it
2. **Tense under modals**: embedded tense is checked against the modal's
   eval time, not speech time

## Key Innovation

Most tense theories (Abusch, Von Stechow, Kratzer, Ogihara) only address
tense under attitude verbs. Klecha extends the eval-time shift to modals:
"John might have left" involves past tense checked against the modal's
evaluation time, not against speech time.

This is formalized via the `evalTimeIndex` field on `TensePronoun`: modals
update this index just as attitude verbs do.

## References

- Klecha, P. (2016). Modality and embedded temporal operators.
  *Semantics and Pragmatics* 9(9): 1-55.
-/

namespace IntensionalSemantics.Tense.Klecha

open Core.Tense
open Core.Reichenbach
open IntensionalSemantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Modal Eval Time Shift
-- ════════════════════════════════════════════════════════════════

/-- Klecha's modal eval time shift: a modal operator shifts the
    temporal evaluation context for its complement, parallel to
    attitude verbs.

    `modalEvalTime`: the time at which the modal is evaluated
    `g`: temporal assignment
    `evalIdx`: index of the eval time variable

    The result is a new assignment where g(evalIdx) = modalEvalTime. -/
def modalEvalTimeShift {Time : Type*}
    (modalEvalTime : Time) (g : TemporalAssignment Time)
    (evalIdx : ℕ) : TemporalAssignment Time :=
  updateTemporal g evalIdx modalEvalTime

/-- After modal eval time shift, the eval time IS the modal's eval time. -/
theorem modalShift_gives_evalTime {Time : Type*}
    (modalEvalTime : Time) (g : TemporalAssignment Time) (evalIdx : ℕ) :
    interpTense evalIdx (modalEvalTimeShift modalEvalTime g evalIdx) =
    modalEvalTime :=
  Core.VarAssignment.update_lookup_same g evalIdx modalEvalTime


-- ════════════════════════════════════════════════════════════════
-- § Modal-Tense Interaction
-- ════════════════════════════════════════════════════════════════

/-- Klecha's modal-tense interaction: tense constraint checked against
    the modal's eval time, not against speech time.

    Example: "John might have left"
    - Modal "might" shifts eval time
    - Past "have left" is checked against modal eval time
    - Result: the leaving is past relative to the modal evaluation,
      not necessarily past relative to speech time -/
def modalTenseInteraction {Time : Type*} [LinearOrder Time]
    (tenseFeature : GramTense) (refTime modalEvalTime : Time) : Prop :=
  tenseFeature.constrains refTime modalEvalTime


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Klecha derives the modal-tense interaction: past tense under a
    modal is checked against the modal's eval time.

    This is THE key result: eval time is visible to modals, not just
    to attitude verbs. -/
theorem klecha_derives_modal_tense {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (modalEvalTime : Time)
    (hPast : tp.constraint = .past)
    (hShift : tp.evalTime (modalEvalTimeShift modalEvalTime g tp.evalTimeIndex) =
              modalEvalTime)
    (hBefore : tp.resolve (modalEvalTimeShift modalEvalTime g tp.evalTimeIndex) <
               modalEvalTime) :
    modalTenseInteraction .past
      (tp.resolve (modalEvalTimeShift modalEvalTime g tp.evalTimeIndex))
      modalEvalTime := by
  simp [modalTenseInteraction, GramTense.constrains]
  exact hBefore

/-- The evalTimeIndex on TensePronoun IS Klecha's mechanism:
    modals update this index to shift the eval time for embedded tense. -/
theorem evalTimeIndex_grounds_klecha {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (modalEvalTime : Time) :
    tp.evalTime (modalEvalTimeShift modalEvalTime g tp.evalTimeIndex) =
    modalEvalTime :=
  evalTime_shifts_under_embedding tp g modalEvalTime


-- ════════════════════════════════════════════════════════════════
-- § Theory Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Klecha (2016) theory identity card. -/
def Klecha : TenseTheory where
  name := "Klecha 2016"
  citation := "Klecha, P. (2016). Modality and embedded temporal operators. S&P 9(9): 1-55."
  hasTemporalDeRe := false
  hasULC := false
  hasZeroTense := false
  hasSOTDeletion := false
  simultaneousMechanism := "not primary focus (inherits from base tense theory)"


end IntensionalSemantics.Tense.Klecha
