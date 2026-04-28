import Linglib.Core.Time.Tense
import Linglib.Theories.Semantics.Modality.TemporalConstraint

/-!
# Tense × Modal Base composition
@cite{klecha-2016}

The four-cell matrix that arises when @cite{klecha-2016}'s modal-base
pronoun temporal constraints (DOX gives RT ≤ EvalT, CIR gives RT > EvalT)
intersect with grammatical tense (PAST gives RT < EvalT, NPST gives
RT ≥ EvalT).

| | DOX (RT ≤ t) | CIR (RT > t) |
|------|-------------|-------------|
| PAST (RT < t) | RT < t (past) | False (impossible) |
| NPST (RT ≥ t) | RT = t (simultaneous) | RT > t (future) |

The four cells are realized as `↔` theorems below. The DOX/PAST cell
gives the genuine past reading of "Martina thought Carissa got pregnant";
DOX/NPST forces simultaneity; CIR/NPST gives the future-oriented reading
of "Martina hoped Carissa got pregnant" (with surface PAST morphology
analyzed as SOT agreement over semantic NPST per @cite{klecha-2016}
§3.3); CIR/PAST is empty.

The `attitudeTemporalConstraint` dispatch and its derivation from
situation-base membership live in
`Theories/Semantics/Modality/TemporalConstraint.lean`. This file is the
*tense-side* projection of that machinery.

## What this file does NOT formalize

The contrast @cite{klecha-2016} draws (§4.1) is between *constraining*
the prejacent's RT vs *binding* the open temporal argument inside the
prejacent. This file formalizes the constraint side only. Klecha's
de se enrichment (§3.4 + Appendix B), where attitudes quantify over
centered histories ⟨y, u, i⟩, is not formalized here. Aspect (PRV/be-ing
per Klecha eq 26), SOT agreement as a transformation, and Double Access
readings (§5.3) are likewise out of scope.
-/

namespace Semantics.Tense.Modal.Matrix

open Core.Time.Tense (GramTense)
open Core.Modality (ModalBaseKind)
open Semantics.Modality.TemporalConstraint (attitudeTemporalConstraint)


/-! ## The four-cell matrix -/

/-- DOX ∧ PAST = past: under a doxastic modal base with semantic past
    tense, the embedded reference time is strictly before the evaluation
    time. Both constraints are satisfiable, and their conjunction is just
    PAST (since RT < t implies RT ≤ t). -/
theorem dox_past_iff {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) :
    attitudeTemporalConstraint .doxastic evalTime refTime ∧
    GramTense.constrains .past refTime evalTime ↔
    refTime < evalTime :=
  ⟨λ ⟨_, hPast⟩ => hPast, λ h => ⟨le_of_lt h, h⟩⟩

/-- CIR ∧ PAST = ⊥: a circumstantial modal base requires RT > t, but
    semantic past tense requires RT < t. The conjunction is empty. The
    surface "past" morphology in "Martina hoped Carissa got pregnant"
    under the future-oriented (CIR) reading is SOT agreement over
    semantic NPST per @cite{klecha-2016} §3.3, not semantic PAST. -/
theorem cir_past_iff_false {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) :
    attitudeTemporalConstraint .circumstantial evalTime refTime ∧
    GramTense.constrains .past refTime evalTime ↔ False :=
  ⟨λ ⟨hGt, hLt⟩ => absurd hLt (not_lt.mpr (le_of_lt hGt)), False.elim⟩

/-- DOX ∧ NPST = simultaneous: a doxastic modal base requires RT ≤ t,
    and non-past tense requires RT ≥ t. The conjunction forces RT = t.
    This is why "Martina thought Carissa was pregnant" with non-past
    (SOT-agreed) gives a simultaneous reading. -/
theorem dox_npst_iff {Time : Type*} [LinearOrder Time]
    (evalTime refTime : Time) :
    attitudeTemporalConstraint .doxastic evalTime refTime ∧
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
    attitudeTemporalConstraint .circumstantial evalTime refTime ∧
    GramTense.constrains .nonpast refTime evalTime ↔
    refTime > evalTime :=
  ⟨λ ⟨hGt, _⟩ => hGt, λ h => ⟨h, le_of_lt h⟩⟩


end Semantics.Tense.Modal.Matrix
