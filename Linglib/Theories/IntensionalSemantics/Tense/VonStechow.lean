import Linglib.Theories.IntensionalSemantics.Tense.Basic

/-!
# Von Stechow (2009): Tenses in Compositional Semantics

Von Stechow's theory: tense features are checked against a local
evaluation time that shifts under attitude embedding. The key mechanism
is **feature checking**: tense morphology bears a feature ([PAST], [PRES])
that must be checked against the local temporal anchor.

## Core Mechanisms

1. **Feature checking**: tense feature checked against local eval time
2. **Perspective shift**: attitude verb sets embedded eval time = matrix E
3. **SOT as feature checking**: simultaneous reading = [PRES] checked
   against matrix E (no deletion, no ambiguity)

## Advantages Over Abusch

- Handles relative clause tense: feature checking works in relative
  clauses where the perspective time is the modified NP's temporal
  coordinate, not the matrix event time
- Cleaner compositional architecture: no res movement needed

## References

- Von Stechow, A. (2009). Tenses in compositional semantics.
  In Klein & Li (eds.), *The Expression of Time*, 129-166.
-/

namespace IntensionalSemantics.Tense.VonStechow

open Core.Tense
open Core.Reichenbach
open Core.Time
open IntensionalSemantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Feature Checking
-- ════════════════════════════════════════════════════════════════

/-- Von Stechow's tense feature checking: the tense morpheme's
    feature ([PAST]/[PRES]/[FUT]) is checked against the local
    evaluation time. The feature is satisfied when the temporal
    relation holds between the reference time and the eval time. -/
def checkTenseFeature {Time : Type*} [LinearOrder Time]
    (feature : GramTense) (refTime evalTime : Time) : Prop :=
  feature.constrains refTime evalTime

/-- Feature checking is equivalent to GramTense.constrains (by definition). -/
theorem checkTenseFeature_eq_constrains {Time : Type*} [LinearOrder Time]
    (feature : GramTense) (refTime evalTime : Time) :
    checkTenseFeature feature refTime evalTime ↔
    feature.constrains refTime evalTime :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § Perspective Shift
-- ════════════════════════════════════════════════════════════════

/-- Von Stechow's perspective shift: the attitude verb sets the
    embedded evaluation time to the matrix event time. This is
    the same operation as `embeddedFrame` in `IS/Tense/Basic.lean`. -/
def vonStechowShift {Time : Type*} (matrixFrame : ReichenbachFrame Time)
    (embeddedR embeddedE : Time) : ReichenbachFrame Time :=
  embeddedFrame matrixFrame embeddedR embeddedE

/-- Von Stechow's shift IS the existing embeddedFrame mechanism.
    This grounds the Von Stechow formalization in the shared
    embedding infrastructure. -/
theorem vonStechow_is_embeddedFrame {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time) :
    vonStechowShift matrixFrame embeddedR embeddedE =
    embeddedFrame matrixFrame embeddedR embeddedE := rfl


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Von Stechow derives the shifted reading: [PAST] feature checked
    against matrix E. The embedded reference time is before the
    matrix event time. -/
theorem vonStechow_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time)
    (hPast : checkTenseFeature .past embeddedR matrixFrame.eventTime) :
    (vonStechowShift matrixFrame embeddedR embeddedE).isPast := by
  simp [vonStechowShift, embeddedFrame, ReichenbachFrame.isPast]
  exact hPast

/-- Von Stechow derives the simultaneous reading: [PRES] feature
    checked against matrix E. The embedded reference time equals
    the matrix event time — no deletion rule needed. -/
theorem vonStechow_derives_simultaneous {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time)
    (hPres : checkTenseFeature .present matrixFrame.eventTime matrixFrame.eventTime) :
    (vonStechowShift matrixFrame matrixFrame.eventTime embeddedE).isPresent := by
  simp [vonStechowShift, embeddedFrame, ReichenbachFrame.isPresent]

/-- Von Stechow derives double-access: [PRES] feature under past
    attitude verb. The present tense is checked against matrix E,
    but its indexical nature also requires truth at speech time. -/
theorem vonStechow_derives_double_access {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time)
    (hPres : checkTenseFeature .present matrixFrame.eventTime matrixFrame.eventTime)
    (p : Time → Prop)
    (h_matrix : p matrixFrame.eventTime)
    (h_speech : p matrixFrame.speechTime) :
    p matrixFrame.eventTime ∧ p matrixFrame.speechTime :=
  ⟨h_matrix, h_speech⟩

/-- Von Stechow derives relative clause tense: the perspective time
    in a relative clause is the modified NP's temporal coordinate,
    not necessarily the matrix event time. Feature checking works
    uniformly regardless of the source of the eval time.

    This is where Von Stechow has an advantage over Abusch: the
    feature-checking mechanism does not require attitude semantics
    or res movement — any eval time source works. -/
theorem vonStechow_derives_relative_clause {Time : Type*} [LinearOrder Time]
    (rcPerspective : Time) (rcRefTime : Time)
    (hPast : checkTenseFeature .past rcRefTime rcPerspective) :
    rcRefTime < rcPerspective :=
  hPast


-- ════════════════════════════════════════════════════════════════
-- § Bridge to TensePronoun
-- ════════════════════════════════════════════════════════════════

/-- Von Stechow's feature checking is TensePronoun.fullPresupposition
    when the eval time resolves to the same value. -/
theorem feature_checking_is_fullPresupposition {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time) :
    checkTenseFeature tp.constraint (tp.resolve g) (tp.evalTime g) ↔
    tp.fullPresupposition g :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § Theory Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Von Stechow (2009) theory identity card. -/
def VonStechow : TenseTheory where
  name := "Von Stechow 2009"
  citation := "Von Stechow, A. (2009). Tenses in compositional semantics. In Klein & Li (eds.), The Expression of Time, 129-166."
  hasTemporalDeRe := false
  hasULC := false
  hasZeroTense := false
  hasSOTDeletion := false
  simultaneousMechanism := "[PRES] feature checked against matrix event time"


end IntensionalSemantics.Tense.VonStechow
