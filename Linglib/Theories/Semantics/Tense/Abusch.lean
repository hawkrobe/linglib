import Linglib.Theories.Semantics.Tense.Basic

/-!
# Abusch (1997): Sequence of Tense and Temporal De Re

Abusch's theory: tense morphemes are temporal pronouns (variables with
presupposed constraints and binding modes). The key innovation is
**temporal de re**: tense can take wide scope over attitude operators
via res movement, just as DPs can scope out of attitude complements.

## Core Mechanisms

1. **Tense as pronoun**: `TensePronoun` with variable index, constraint, mode
2. **Relation transmission**: attitude verb transmits event time as new eval time
3. **Upper Limit Constraint (ULC)**: embedded R ≤ matrix E (from branching futures)
4. **Temporal de re**: tense variable in res position of attitude

## Derivation Theorems

- Shifted reading: free past variable with presupposition against eval time
- Simultaneous reading: bound variable receives matrix event time
- Double-access: indexical present + attitude binding
- ULC: blocks forward-shifted readings
- Temporal de re: res movement for wide-scope tense

## Limitations

- Relative clause tense: Sharvit's challenge (the mechanism doesn't
  extend straightforwardly to relative clauses where the tense takes
  the perspective of a participant)
- Modal-tense interaction: not addressed in original framework
- Counterfactual tense: not addressed

## References

- Abusch, D. (1997). Sequence of tense and temporal de re.
  *Linguistics and Philosophy* 20(1): 1–50.
- Sharvit, Y. (2003). Trying to be progressive. *NELS 33*.
-/

namespace IntensionalSemantics.Tense.Abusch

open Core.Tense
open Core.Reichenbach
open Core.Time
open IntensionalSemantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Temporal De Re
-- ════════════════════════════════════════════════════════════════

/-- Abusch's temporal de re: a tense variable can take wide scope
    over an attitude operator by occupying the res position.

    The res has three components:
    - `referent`: the time denoted (resolved in the matrix context)
    - `evalTime`: the evaluation time in the embedded context
    - `constraint`: the presupposed temporal relation

    This parallels individual de re: "John believes the president is wise"
    where "the president" is evaluated in the actual world, not in John's
    belief worlds. Similarly, temporal de re evaluates tense in the
    matrix temporal context. -/
structure TemporalDeRe (Time : Type*) where
  /-- The time referred to (resolved in matrix context) -/
  referent : Time
  /-- The evaluation time (shifted by attitude) -/
  evalTime : Time
  /-- The temporal constraint (past/present/future) -/
  constraint : GramTense

/-- A temporal de re is felicitous when the constraint is satisfied
    in the matrix context (referent checked against matrix eval time). -/
def TemporalDeRe.isFelicitous {Time : Type*} [LinearOrder Time]
    (dr : TemporalDeRe Time) : Prop :=
  dr.constraint.constrains dr.referent dr.evalTime


-- ════════════════════════════════════════════════════════════════
-- § Relation Transmission
-- ════════════════════════════════════════════════════════════════

/-- Abusch's relation transmission: an attitude verb transmits its event
    time as the new evaluation time for the embedded clause.
    This is the semantic effect of the attitude on temporal interpretation. -/
def relationTransmission {Time : Type*} (matrixFrame : ReichenbachFrame Time)
    (g : TemporalAssignment Time) (evalIdx : ℕ) : TemporalAssignment Time :=
  updateTemporal g evalIdx matrixFrame.eventTime

/-- After relation transmission, the eval time IS the matrix event time. -/
theorem relationTransmission_shifts_eval {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (g : TemporalAssignment Time)
    (evalIdx : ℕ) :
    interpTense evalIdx (relationTransmission matrixFrame g evalIdx) =
    matrixFrame.eventTime :=
  Core.VarAssignment.update_lookup_same g evalIdx matrixFrame.eventTime

/-- Relation transmission = updating the eval time index on TensePronoun.
    This bridges Abusch's mechanism to the `evalTimeIndex` field. -/
theorem relationTransmission_is_evalTime_update {Time : Type*}
    (tp : TensePronoun) (matrixFrame : ReichenbachFrame Time)
    (g : TemporalAssignment Time) :
    tp.evalTime (relationTransmission matrixFrame g tp.evalTimeIndex) =
    matrixFrame.eventTime := by
  simp [TensePronoun.evalTime, relationTransmission, interpTense,
    Core.VarAssignment.lookupVar, updateTemporal, Core.VarAssignment.updateVar]


-- ════════════════════════════════════════════════════════════════
-- § Upper Limit Constraint
-- ════════════════════════════════════════════════════════════════

/-- Abusch's ULC: in intensional contexts, tense reference cannot
    exceed the local evaluation time. From branching futures: at the
    attitude event time, future branches diverge, so no time beyond
    the attitude time is accessible across all doxastic alternatives. -/
def abuschiULC {Time : Type*} [LE Time]
    (embeddedR evalTime : Time) : Prop :=
  upperLimitConstraint embeddedR evalTime

/-- The ULC is equivalent to the shared formulation. -/
theorem abuschiULC_eq_ulc {Time : Type*} [LE Time]
    (embeddedR evalTime : Time) :
    abuschiULC embeddedR evalTime ↔ upperLimitConstraint embeddedR evalTime :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Abusch derives the shifted reading: a free past variable with
    presupposition checked against the (shifted) eval time.
    The past constraint gives R < evalTime = matrixE. -/
theorem abusch_derives_shifted {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (_hPast : tp.constraint = .past)
    (hPresup : tp.resolve g < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPast := by
  simp [embeddedFrame, ReichenbachFrame.isPast]
  exact hPresup

/-- Abusch derives the simultaneous reading: a bound variable receives
    the matrix event time via lambda abstraction. -/
theorem abusch_derives_simultaneous {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time)
    (hBind : tp.resolve g = matrixFrame.eventTime) :
    (embeddedFrame matrixFrame (tp.resolve g) (tp.resolve g)).isPresent := by
  simp [embeddedFrame, ReichenbachFrame.isPresent, hBind]

/-- Abusch derives the simultaneous reading via the bound variable mechanism:
    updating the temporal assignment so the tense variable receives matrix E. -/
theorem abusch_derives_simultaneous_via_binding {Time : Type*}
    (tp : TensePronoun) (g : TemporalAssignment Time)
    (matrixFrame : ReichenbachFrame Time) :
    tp.resolve (updateTemporal g tp.varIndex matrixFrame.eventTime) =
    matrixFrame.eventTime :=
  tp.bound_resolve_eq_binder g matrixFrame.eventTime

/-- Abusch derives double-access: indexical present requires truth at
    BOTH speech time (indexical rigidity) AND matrix event time
    (attitude accessibility). -/
theorem abusch_derives_double_access {Time : Type*}
    (p : Time → Prop) (speechTime matrixEventTime : Time)
    (h_speech : p speechTime) (h_matrix : p matrixEventTime) :
    doubleAccess p speechTime matrixEventTime :=
  ⟨h_speech, h_matrix⟩

/-- Abusch's ULC blocks the forward-shifted reading:
    if R > evalTime, the ULC (R ≤ evalTime) is violated. -/
theorem abusch_blocks_forward_shift {Time : Type*} [LinearOrder Time]
    (embeddedR matrixE : Time)
    (h_ulc : abuschiULC embeddedR matrixE)
    (h_forward : embeddedR > matrixE) : False :=
  ulc_blocks_forward_shift embeddedR matrixE h_ulc h_forward

/-- Abusch derives temporal de re: the tense variable in res position
    is evaluated in the matrix context, giving wide-scope temporal
    reference. When the res referent satisfies the past constraint
    against the matrix eval time, the de re reading is felicitous. -/
theorem abusch_derives_temporal_de_re {Time : Type*} [LinearOrder Time]
    (dr : TemporalDeRe Time)
    (hPast : dr.constraint = .past)
    (hBefore : dr.referent < dr.evalTime) :
    dr.isFelicitous := by
  simp [TemporalDeRe.isFelicitous, GramTense.constrains, hPast]
  exact hBefore


-- ════════════════════════════════════════════════════════════════
-- § Theory Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Abusch (1997) theory identity card. -/
def Abusch : TenseTheory where
  name := "Abusch 1997"
  citation := "Abusch, D. (1997). Sequence of tense and temporal de re. L&P 20(1): 1-50."
  hasTemporalDeRe := true
  hasULC := true
  hasZeroTense := false
  hasSOTDeletion := false
  simultaneousMechanism := "bound variable receives matrix event time"


end IntensionalSemantics.Tense.Abusch
