import Linglib.Core.Modality.ModalBaseKind
import Linglib.Core.Temporal.Tense
import Linglib.Core.Lexical.VerbClass
import Linglib.Core.Modality.ModalTypes

/-!
# Modal Base Temporal Constraints
@cite{klecha-2016}

History predicates, temporal constraints on embedded reference time, and
bridges from `Attitude` / `ModalFlavor` to `ModalBaseKind`.

Klecha's key insight: the temporal orientation of a modal is determined by
the temporal structure of its accessible histories, which is encoded in the
modal base pronoun:

- **DOX** (doxastic): returns *actual histories* ending at the eval time.
  Time component: `(-∞, t]`. → RT ≤ EvalT (Upper Limit Constraint).
- **CIR** (circumstantial): returns *future histories* departing from the
  eval time. Time component: `(t, ∞)`. → RT > EvalT (future orientation).

The Upper Limit Constraint is DERIVED from DOX's temporal character, not
stipulated as a separate principle.
-/

namespace Semantics.Modality.TemporalConstraint

open Core.Modality (ModalBaseKind)

/-! ## Partial History Taxonomy

@cite{klecha-2016} Definition 3 defines five kinds of partial history,
distinguished by the temporal component of the world-time pair relative
to a reference time `t`. We formalize all five as predicates on time
pairs. Only actual and future are used in the core DOX/CIR mechanism,
but the full taxonomy is needed for extensions (e.g., prospective = the
basis of `BranchingTime.historicalBase`). -/

/-- Maximal history: unrestricted temporal extent.
    @cite{klecha-2016} Definition 3(v): Ω_t = all histories. -/
def isMaximalHistory {Time : Type*} (_evalTime _historyTime : Time) : Prop :=
  True

/-- Actual history: temporal component ends at or before `t`.
    @cite{klecha-2016} Definition 3(vi): 𝒜_t = {i : τ(i) = (-∞, t]}. -/
def isActualHistory {Time : Type*} [LE Time]
    (evalTime historyTime : Time) : Prop :=
  historyTime ≤ evalTime

/-- Past history: temporal component ends strictly before `t`.
    @cite{klecha-2016} Definition 3(viii): 𝒫_t = {i : τ(i) = (-∞, t)}.
    Distinct from actual: past excludes `t` itself. -/
def isPastHistory {Time : Type*} [LT Time]
    (evalTime historyTime : Time) : Prop :=
  historyTime < evalTime

/-- Future history: temporal component starts strictly after `t`.
    @cite{klecha-2016} Definition 3(vii): ℱ_t = {j : τ(j) = (t, ∞)}. -/
def isFutureHistory {Time : Type*} [LT Time]
    (evalTime historyTime : Time) : Prop :=
  historyTime > evalTime

/-- Prospective history: temporal component starts at or after `t`.
    @cite{klecha-2016} Definition 3(ix): ℙ_t = {j : τ(j) = [t, ∞)}.
    This is exactly the temporal component of `BranchingTime.historicalBase`:
    `s'.time ≥ s.time`. -/
def isProspectiveHistory {Time : Type*} [LE Time]
    (evalTime historyTime : Time) : Prop :=
  historyTime ≥ evalTime

/-- Actual and future histories are complementary: every time is
    either ≤ t (actual) or > t (future). -/
theorem actual_future_complementary {Time : Type*} [LinearOrder Time]
    (evalTime historyTime : Time) :
    isActualHistory evalTime historyTime ∨ isFutureHistory evalTime historyTime :=
  (lt_or_ge evalTime historyTime).elim Or.inr Or.inl

/-- Past and prospective histories are complementary: every time is
    either < t (past) or ≥ t (prospective). -/
theorem past_prospective_complementary {Time : Type*} [LinearOrder Time]
    (evalTime historyTime : Time) :
    isPastHistory evalTime historyTime ∨ isProspectiveHistory evalTime historyTime :=
  (lt_or_ge historyTime evalTime).elim Or.inl Or.inr

/-- Past ⊂ actual: strict past implies actual. -/
theorem past_implies_actual {Time : Type*} [Preorder Time]
    (evalTime historyTime : Time) (h : isPastHistory evalTime historyTime) :
    isActualHistory evalTime historyTime :=
  le_of_lt h

/-- Future ⊂ prospective: strict future implies prospective. -/
theorem future_implies_prospective {Time : Type*} [Preorder Time]
    (evalTime historyTime : Time) (h : isFutureHistory evalTime historyTime) :
    isProspectiveHistory evalTime historyTime :=
  le_of_lt h

/-- Actual ∩ prospective = simultaneous: a time that is both actual
    and prospective is exactly the evaluation time. -/
theorem actual_and_prospective_iff_simultaneous {Time : Type*} [PartialOrder Time]
    (evalTime historyTime : Time) :
    isActualHistory evalTime historyTime ∧ isProspectiveHistory evalTime historyTime ↔
    historyTime = evalTime :=
  ⟨λ ⟨hle, hge⟩ => le_antisymm hle hge, λ h => ⟨le_of_eq h, ge_of_eq h⟩⟩

/-- Past and future are disjoint: no time is both < t and > t. -/
theorem past_future_disjoint {Time : Type*} [Preorder Time]
    (evalTime historyTime : Time) :
    ¬(isPastHistory evalTime historyTime ∧ isFutureHistory evalTime historyTime) := by
  intro ⟨h1, h2⟩
  exact lt_asymm h1 h2


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

/-- `permitsCircumstantial` ↔ `toModalBaseKind = .circumstantial`. -/
theorem permitsCirc_iff_cir (a : Core.Verbs.Attitude) :
    a.permitsCircumstantial = true ↔
    Attitude.toModalBaseKind a = ModalBaseKind.circumstantial := by
  cases a <;> simp [Core.Verbs.Attitude.permitsCircumstantial, Attitude.toModalBaseKind]


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
