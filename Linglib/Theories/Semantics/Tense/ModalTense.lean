import Linglib.Core.Temporal.Tense
import Linglib.Theories.Semantics.Modality.TemporalConstraint

/-!
# @cite{klecha-2016}: Modality and Embedded Temporal Operators
@cite{klecha-2016}

Klecha's theory of how modals and attitude verbs constrain the temporal
possibilities of their prejacents. The central claim: temporal orientation
is determined by the *modal base pronoun* (DOX vs. CIR), not by the
modal or attitude verb per se.

## Core Mechanism

Modals quantify over partial histories — world-time pairs where the time
component is an interval. Different modal base pronouns return different
kinds of history:

1. **DOX** (doxastic): returns *actual histories* ending at the eval time.
   Embedded tense must locate RT within this interval → RT ≤ EvalT.
   This derives the Upper Limit Constraint compositionally.

2. **CIR** (circumstantial): returns *future histories* departing from
   the eval time. Embedded tense locates RT after this point → RT > EvalT.
   This permits future-oriented readings under *hope*, *pray*, etc.

## What this file does NOT claim

Klecha does NOT propose that modals "shift" the evaluation time (that is
@cite{abusch-2004} and @cite{katz-2001}). Rather, modals *constrain* the
RT of their prejacent at a distance: the temporal structure of the
accessible histories limits what RT values are compatible. The embedded
tense is still independently introduced; the modal merely narrows which
RTs satisfy both the tense presupposition and the modal's domain.

## Attitude verb predictions

- **think** takes DOX only → imposes upper limit (past/present only)
- **hope** can take CIR → permits future orientation
- **believe** takes DOX only → imposes upper limit
- **pray** can take CIR → permits future orientation

The `evalTimeIndex` mechanism (from `Core.Tense`) handles the separate
question of how attitude verbs transmit their evaluation time to the
embedded clause. That mechanism is orthogonal to Klecha's modal base
constraint.

-/

namespace Semantics.Tense.ModalTense

open Core.Tense
open Core.Reichenbach
open Semantics.Modality.TemporalConstraint (attitudeTemporalConstraint
  doxConstrainsRT cirConstrainsRT
  dox_compatible_with_past dox_incompatible_with_future cir_compatible_with_future)
open Core.Modality (ModalBaseKind)
open Core.Tense (GramTense)


-- ════════════════════════════════════════════════════════════════
-- § Modal Base Kind determines temporal orientation
-- ════════════════════════════════════════════════════════════════

/-- The temporal constraint on embedded RT, given the modal base kind
    and the modal's evaluation time.

    This is the key compositional link: the modal base pronoun's temporal
    character (DOX vs. CIR) determines what RT values are available to the
    embedded tense. -/
def embeddedRTConstraint {Time : Type*} [LinearOrder Time]
    (kind : ModalBaseKind) (modalEvalTime embeddedRT : Time) : Prop :=
  attitudeTemporalConstraint kind modalEvalTime embeddedRT


-- ════════════════════════════════════════════════════════════════
-- § Think: DOX-only → upper limit
-- ════════════════════════════════════════════════════════════════

/-- *think* takes only a doxastic modal base. The embedded RT must be
    at or before the thinking time.

    "Martina thought Carissa got pregnant" → embedded RT ≤ thinking time.
    Future-oriented readings are blocked. -/
theorem think_blocks_future {Time : Type*} [LinearOrder Time]
    (thinkTime embeddedRT : Time) (hFut : embeddedRT > thinkTime) :
    ¬ embeddedRTConstraint .doxastic thinkTime embeddedRT :=
  dox_incompatible_with_future thinkTime embeddedRT hFut

/-- *think* permits past-oriented embedded tense. -/
theorem think_permits_past {Time : Type*} [LinearOrder Time]
    (thinkTime embeddedRT : Time) (hPast : embeddedRT < thinkTime) :
    embeddedRTConstraint .doxastic thinkTime embeddedRT :=
  dox_compatible_with_past thinkTime embeddedRT hPast

/-- *think* permits simultaneous (present) embedded tense.
    RT = EvalT satisfies the doxastic constraint RT ≤ EvalT. -/
theorem think_permits_simultaneous {Time : Type*} [LinearOrder Time]
    (thinkTime : Time) :
    embeddedRTConstraint .doxastic thinkTime thinkTime :=
  le_refl thinkTime


-- ════════════════════════════════════════════════════════════════
-- § Hope: CIR → future orientation
-- ════════════════════════════════════════════════════════════════

/-- *hope* can take a circumstantial modal base. The embedded RT can be
    after the hoping time.

    "Martina hoped Carissa got pregnant" → with CIR, embedded RT > hoping time.
    The "past" morphology on "got" is SOT agreement, not semantic past. -/
theorem hope_permits_future {Time : Type*} [LinearOrder Time]
    (hopeTime embeddedRT : Time) (hFut : embeddedRT > hopeTime) :
    embeddedRTConstraint .circumstantial hopeTime embeddedRT :=
  cir_compatible_with_future hopeTime embeddedRT hFut


-- ════════════════════════════════════════════════════════════════
-- § Hope: DOX → past orientation
-- ════════════════════════════════════════════════════════════════

/-- *hope* can ALSO take a doxastic modal base (§3.2: "I hope she
    already left"). Under DOX, the embedded RT must be at or before the
    hoping time, giving a past-oriented reading. Preferential attitudes
    are compatible with both DOX and CIR. -/
theorem hope_permits_past {Time : Type*} [LinearOrder Time]
    (hopeTime embeddedRT : Time) (hPast : embeddedRT < hopeTime) :
    embeddedRTConstraint .doxastic hopeTime embeddedRT :=
  dox_compatible_with_past hopeTime embeddedRT hPast


-- ════════════════════════════════════════════════════════════════
-- § Compositional intersection: tense × modal base
-- ════════════════════════════════════════════════════════════════

/-! The central predictions of @cite{klecha-2016}'s theory emerge from
composing tense constraints with modal base constraints. Each cell in
the matrix is the intersection of the two requirements:

| | DOX (RT ≤ t) | CIR (RT > t) |
|------|-------------|-------------|
| PAST (RT < t) | RT < t (past) | ⊥ (impossible) |
| NPST (RT ≥ t) | RT = t (simultaneous) | RT > t (future) |

These four theorems derive all of Table 1's predictions. -/

/-- DOX ∧ PAST = past: under a doxastic modal base with past tense,
    the embedded reference time is strictly before the evaluation time.
    Both constraints are satisfiable, and the conjunction is just PAST. -/
theorem dox_past_iff {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) :
    embeddedRTConstraint .doxastic evalTime refTime ∧
    GramTense.constrains .past refTime evalTime ↔
    refTime < evalTime :=
  ⟨λ ⟨_, hPast⟩ => hPast, λ h => ⟨le_of_lt h, h⟩⟩

/-- CIR ∧ PAST = impossible: a circumstantial modal base requires
    RT > t, but past tense requires RT < t. The conjunction is empty.
    This is why "John hoped Carissa got pregnant" cannot have a past-
    oriented reading under CIR. -/
theorem cir_past_impossible {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) :
    ¬(embeddedRTConstraint .circumstantial evalTime refTime ∧
      GramTense.constrains .past refTime evalTime) :=
  λ ⟨hGt, hLt⟩ => absurd hLt (not_lt.mpr (le_of_lt hGt))

/-- DOX ∧ NPST = simultaneous: a doxastic modal base requires RT ≤ t,
    and non-past tense requires RT ≥ t. The conjunction forces RT = t.
    This is why "Martina thought Carissa was pregnant" with non-past
    (SOT-agreed) gives a simultaneous reading. -/
theorem dox_npst_iff {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) :
    embeddedRTConstraint .doxastic evalTime refTime ∧
    GramTense.constrains .nonpast refTime evalTime ↔
    refTime = evalTime :=
  ⟨λ ⟨hLe, hGe⟩ => le_antisymm hLe hGe,
   λ h => ⟨le_of_eq h, ge_of_eq h⟩⟩

/-- CIR ∧ NPST = future: a circumstantial modal base requires RT > t,
    and non-past tense requires RT ≥ t. The conjunction is RT > t.
    This is why "Martina hoped Carissa got pregnant" with non-past
    (SOT-agreed) gives a future-oriented reading under CIR. -/
theorem cir_npst_iff {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) :
    embeddedRTConstraint .circumstantial evalTime refTime ∧
    GramTense.constrains .nonpast refTime evalTime ↔
    refTime > evalTime :=
  ⟨λ ⟨hGt, _⟩ => hGt, λ h => ⟨h, le_of_lt h⟩⟩


-- ════════════════════════════════════════════════════════════════
-- § Eval time shift (orthogonal mechanism)
-- ════════════════════════════════════════════════════════════════

/-- Attitude verbs transmit their event time as the embedded clause's
    evaluation time via the `evalTimeIndex` mechanism. This is orthogonal
    to the modal base constraint: it determines WHAT time the modal base
    is evaluated at, while the modal base kind determines what DIRECTION
    of temporal reference is available from that time.

    In root clauses: evalTimeIndex = 0 → g(0) = speech time.
    Under embedding: evalTimeIndex updated → g(idx) = matrix event time. -/
def modalEvalTimeShift {Time : Type*}
    (modalEvalTime : Time) (g : TemporalAssignment Time)
    (evalIdx : ℕ) : TemporalAssignment Time :=
  updateTemporal g evalIdx modalEvalTime

/-- After eval time shift, the eval time IS the modal's eval time. -/
theorem modalShift_gives_evalTime {Time : Type*}
    (modalEvalTime : Time) (g : TemporalAssignment Time) (evalIdx : ℕ) :
    interpTense evalIdx (modalEvalTimeShift modalEvalTime g evalIdx) =
    modalEvalTime :=
  Core.VarAssignment.update_lookup_same g evalIdx modalEvalTime


-- ════════════════════════════════════════════════════════════════
-- § Combined: eval time shift + modal base constraint
-- ════════════════════════════════════════════════════════════════

/-- The full picture for embedded tense under an attitude verb:
    (1) The attitude verb shifts the eval time via `evalTimeIndex`.
    (2) The modal base kind constrains embedded RT relative to the
        shifted eval time.

    For *think*: shift + DOX → RT ≤ thinkTime (upper limit).
    For *hope*: shift + CIR → RT > hopeTime (future orientation). -/
theorem combined_think_upper_limit {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (thinkTime : Time)
    (_hShift : tp.evalTime (modalEvalTimeShift thinkTime g tp.evalTimeIndex) =
               thinkTime)
    (hFut : tp.resolve (modalEvalTimeShift thinkTime g tp.evalTimeIndex) >
            thinkTime) :
    ¬ embeddedRTConstraint .doxastic thinkTime
      (tp.resolve (modalEvalTimeShift thinkTime g tp.evalTimeIndex)) :=
  dox_incompatible_with_future thinkTime _ hFut

/-- The `evalTimeIndex` grounds the eval time shift. -/
theorem evalTimeIndex_grounds_shift {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (modalEvalTime : Time) :
    tp.evalTime (modalEvalTimeShift modalEvalTime g tp.evalTimeIndex) =
    modalEvalTime :=
  evalTime_shifts_under_embedding tp g modalEvalTime


end Semantics.Tense.ModalTense
