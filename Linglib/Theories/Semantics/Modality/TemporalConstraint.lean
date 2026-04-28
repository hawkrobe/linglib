import Linglib.Core.Modality.ModalBaseKind
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Core.Lexical.VerbClass
import Linglib.Core.Modality.ModalTypes

/-!
# Modal Base Temporal Constraints
@cite{klecha-2016}

Klecha-namespace dispatch on `ModalBaseKind` for the temporal constraints
that fall out of @cite{klecha-2016}'s modal-base-pronoun architecture, plus
bridges from `Attitude` / `ModalFlavor` to `ModalBaseKind`.

The framework-neutral interval predicates (`isActualHistory`,
`isFutureHistory`, etc.) and the situation-base derivation theorems live
in `Core.Modality.HistoricalAlternatives`. This file's role is the
Klecha-specific projection: dispatch on `ModalBaseKind` to select between
the actual-history (RT ≤ EvalT) and future-history (RT > EvalT)
constraints.

Klecha's key insight: the temporal orientation of a modal is determined
by the temporal structure of its accessible histories, which is encoded
in the modal base pronoun:

- **DOX** (doxastic): returns *actual histories* ending at the eval
  time. → RT ≤ EvalT (Upper Limit Constraint).
- **CIR** (circumstantial): returns *future histories* departing from
  the eval time. → RT > EvalT (future orientation).

The ULC is **derived** by `.2` projection from `actualHistoryBase`
membership (see `actualHistoryBase_derives_ulc` in
`Core.Modality.HistoricalAlternatives`); the dispatch theorem
`attitudeTemporalConstraint_derived_doxastic` below makes the
Klecha-namespace face of that derivation kernel-checked.
-/

namespace Semantics.Modality.TemporalConstraint

open Core.Modality (ModalBaseKind)
open Core.Modality.HistoricalAlternatives
  (isActualHistory isFutureHistory actualHistoryBase futureHistoryBase
   actualHistoryBase_time_actual futureHistoryBase_time_future
   WorldHistory)


/-! ## Temporal Constraints on Embedded RT -/

/-- Doxastic temporal constraint: embedded reference time must be an actual
    time relative to the modal's evaluation time (RT ≤ EvalT).

    This is the compositional source of the Upper Limit Constraint.
    @cite{klecha-2016} derives it from DOX's temporal character: since DOX
    returns actual histories (ending at t), the embedded event must be
    located within that interval. -/
def doxConstrainsRT {Time : Type*} [LE Time]
    (evalTime refTime : Time) : Prop :=
  isActualHistory evalTime refTime

/-- Circumstantial temporal constraint: embedded reference time must be a
    future time relative to the modal's evaluation time (RT > EvalT).

    This is what permits future-oriented readings under *hope*, *pray*,
    and circumstantial/teleological/deontic modals.
    @cite{klecha-2016} derives it from CIR's temporal character: since CIR
    returns future histories (departing from t), the embedded event must be
    located after that time. -/
def cirConstrainsRT {Time : Type*} [LT Time]
    (evalTime refTime : Time) : Prop :=
  isFutureHistory evalTime refTime

/-- The doxastic constraint IS the upper limit: RT ≤ EvalT. -/
theorem dox_is_upper_limit {Time : Type*} [LE Time]
    (evalTime refTime : Time) :
    doxConstrainsRT evalTime refTime ↔ refTime ≤ evalTime :=
  Iff.rfl

/-- The circumstantial constraint permits future reference: RT > EvalT. -/
theorem cir_permits_future_ref {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time)
    (h : cirConstrainsRT evalTime refTime) :
    ¬ refTime ≤ evalTime :=
  not_le.mpr h

/-- Attitude verbs compatible with DOX impose an upper limit; those
    compatible with CIR do not. This is Klecha's central result: the
    temporal constraint varies with the modal base, not the attitude verb
    per se.

    `think` → DOX only → upper limit
    `hope` → CIR (or DOX) → no upper limit with CIR -/
def attitudeTemporalConstraint {Time : Type*} [LinearOrder Time]
    (kind : ModalBaseKind) (evalTime refTime : Time) : Prop :=
  match kind with
  | .doxastic => doxConstrainsRT evalTime refTime
  | .circumstantial => cirConstrainsRT evalTime refTime

/-- Under DOX, past tense is compatible (RT < EvalT → RT ≤ EvalT). -/
theorem dox_compatible_with_past {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) (hPast : refTime < evalTime) :
    attitudeTemporalConstraint .doxastic evalTime refTime :=
  le_of_lt hPast

/-- Under DOX, future tense is incompatible (RT > EvalT → ¬ RT ≤ EvalT). -/
theorem dox_incompatible_with_future {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) (hFut : refTime > evalTime) :
    ¬ attitudeTemporalConstraint .doxastic evalTime refTime :=
  not_le.mpr hFut

/-- Under CIR, future tense is compatible (RT > EvalT). -/
theorem cir_compatible_with_future {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) (hFut : refTime > evalTime) :
    attitudeTemporalConstraint .circumstantial evalTime refTime :=
  hFut


/-! ## Klecha 2016: constraint as derivation, not stipulation

The two theorems below make @cite{klecha-2016}'s central architectural
claim kernel-checked: `attitudeTemporalConstraint` is *derived* from
membership in the corresponding situation-base (`actualHistoryBase` for
DOX, `futureHistoryBase` for CIR), not stipulated.

This is the formal contrast with @cite{abusch-1997}'s ULC, which is
stipulated as a presupposition on T-nodes; here, ULC follows by `.2`
projection through the situation-base definition. The substrate
derivation lives in `Core.Modality.HistoricalAlternatives` as
`actualHistoryBase_time_actual` / `futureHistoryBase_time_future`;
these theorems re-express it in the Klecha-namespace
`attitudeTemporalConstraint` form. -/

/-- @cite{klecha-2016} eq (35a): DOX returns the actual history base.
    Membership in `actualHistoryBase` derives the doxastic temporal
    constraint (Upper Limit Constraint) by `.2` projection. -/
theorem attitudeTemporalConstraint_derived_doxastic
    {W Time : Type*} [LinearOrder Time]
    (history : WorldHistory W Time)
    (s s' : Core.WorldTimeIndex W Time)
    (h : s' ∈ actualHistoryBase history s) :
    attitudeTemporalConstraint .doxastic s.time s'.time :=
  actualHistoryBase_time_actual history s s' h

/-- @cite{klecha-2016} eq (35b): CIR returns the future history base.
    Membership in `futureHistoryBase` derives the circumstantial
    temporal constraint (future orientation) by `.2` projection. -/
theorem attitudeTemporalConstraint_derived_circumstantial
    {W Time : Type*} [LinearOrder Time]
    (history : WorldHistory W Time)
    (s s' : Core.WorldTimeIndex W Time)
    (h : s' ∈ futureHistoryBase history s) :
    attitudeTemporalConstraint .circumstantial s.time s'.time :=
  futureHistoryBase_time_future history s s' h


/-! ## Attitude → ModalBaseKind bridge -/

/-- Derive `ModalBaseKind` from `Attitude` classification.
    @cite{klecha-2016}: doxastic attitudes select DOX, preferential attitudes
    select CIR. The derived kind determines temporal orientation.

    Note: preferential attitudes CAN also take DOX (e.g., "I hope she
    already left" = DOX → past reading). This function returns the kind
    that distinguishes them: the kind that PERMITS future orientation. -/
def Attitude.toModalBaseKind : Core.Verbs.Attitude → ModalBaseKind
  | .doxastic _ => ModalBaseKind.doxastic
  | .preferential _ => ModalBaseKind.circumstantial

/-- Doxastic attitudes select DOX. -/
theorem doxastic_selects_dox (v : Core.Verbs.Veridicality) :
    Attitude.toModalBaseKind (.doxastic v) = ModalBaseKind.doxastic := rfl

/-- Preferential attitudes select CIR (= can access future histories). -/
theorem preferential_selects_cir (k : Core.Verbs.Preferential) :
    Attitude.toModalBaseKind (.preferential k) = ModalBaseKind.circumstantial := rfl

/-- `PermitsCircumstantial` ↔ `toModalBaseKind = .circumstantial`. -/
theorem permitsCirc_iff_cir (a : Core.Verbs.Attitude) :
    a.PermitsCircumstantial ↔
    Attitude.toModalBaseKind a = ModalBaseKind.circumstantial := by
  cases a <;> simp [Core.Verbs.Attitude.PermitsCircumstantial, Attitude.toModalBaseKind]


/-! ## ModalFlavor → ModalBaseKind bridge

@cite{klecha-2016} Table 1: the temporal orientation of a modal correlates
with its flavor. Epistemic modals are past/present-oriented (DOX-like);
circumstantial, deontic, bouletic, and teleological modals are
future-oriented (CIR-like). This function bridges the four-way
`ModalFlavor` classification (from `Core.Modality`) to Klecha's binary
`ModalBaseKind`. -/

open Core.Modality (ModalFlavor)

/-- Map modal flavor to modal base kind.
    Epistemic → DOX (past/present orientation).
    Circumstantial, deontic, bouletic → CIR (future orientation). -/
def ModalFlavor.toModalBaseKind : ModalFlavor → ModalBaseKind
  | .epistemic => .doxastic
  | .circumstantial => .circumstantial
  | .deontic => .circumstantial
  | .bouletic => .circumstantial

/-- Epistemic modals are DOX-like. -/
theorem epistemic_is_dox : ModalFlavor.toModalBaseKind .epistemic = .doxastic := rfl

/-- Circumstantial modals are CIR-like. -/
theorem circumstantial_is_cir :
    ModalFlavor.toModalBaseKind .circumstantial = ModalBaseKind.circumstantial := rfl

/-- Deontic modals are CIR-like. -/
theorem deontic_is_cir :
    ModalFlavor.toModalBaseKind .deontic = ModalBaseKind.circumstantial := rfl

/-- Bouletic modals are CIR-like. -/
theorem bouletic_is_cir :
    ModalFlavor.toModalBaseKind .bouletic = ModalBaseKind.circumstantial := rfl

/-- Table 1 consequence: epistemic modals block future orientation. -/
theorem epistemic_blocks_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .epistemic) .future = false := rfl

/-- Table 1 consequence: circumstantial modals permit future orientation. -/
theorem circumstantial_permits_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .circumstantial) .future = true := rfl

/-- Table 1 consequence: deontic modals permit future orientation. -/
theorem deontic_permits_future :
    ModalBaseKind.permitsOrientation
      (ModalFlavor.toModalBaseKind .deontic) .future = true := rfl

/-- All non-epistemic flavors map to CIR. -/
theorem non_epistemic_is_cir (f : ModalFlavor) (h : f ≠ .epistemic) :
    ModalFlavor.toModalBaseKind f = ModalBaseKind.circumstantial := by
  cases f <;> simp_all [ModalFlavor.toModalBaseKind]

end Semantics.Modality.TemporalConstraint
