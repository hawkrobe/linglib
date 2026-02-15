import Linglib.Phenomena.SequenceOfTense.Data
import Linglib.Theories.TruthConditional.Sentence.Tense.SequenceOfTense
import Linglib.Theories.TruthConditional.Sentence.Tense.TenseAspectComposition

/-!
# Sequence of Tense: Bridge Theorems

Connects the empirical data in `Data.lean` (Reichenbach frames for SOT examples)
to the theoretical analysis in `SequenceOfTense.lean` (perspective shifting,
available readings, embedded frames).

## Bridge Structure

1. **Frame verification**: Data frames satisfy the expected tenses via `satisfiesTense`
2. **Constructor matching**: `simultaneousFrame`/`shiftedFrame` reproduce the data frames
3. **SOT parameter**: English (`.relative`) vs Japanese (`.absolute`) reading availability
4. **composeTense derivation**: Past-under-past yields overall past for both readings
5. **Aspect–tense pipeline**: Cross-framework `EventPred → PointPred → SitProp → Prop` composition
6. **evalPast ↔ PAST**: Point-level tense evaluation agrees with situation-level tense operators
7. **Reichenbach–aspect correspondence**: Data frames satisfy perfective assumptions used in derivations

## References

- Ogihara, T. (1989/1996). Tense, Attitudes, and Scope. Kluwer.
- Von Stechow, A. (2009). Tenses in compositional semantics.
-/

namespace Phenomena.SequenceOfTense.Bridge

open Core.Reichenbach
open TruthConditional.Sentence.Tense (satisfiesTense SOTParameter)
open TruthConditional.Sentence.Tense.SequenceOfTense
open Phenomena.SequenceOfTense


-- ════════════════════════════════════════════════════════════════
-- § Frame Verification via satisfiesTense
-- ════════════════════════════════════════════════════════════════

/-- The matrix "said" frame satisfies PAST. -/
theorem matrixSaid_is_past :
    satisfiesTense .past matrixSaid = true := by native_decide

/-- The simultaneous embedded frame satisfies PRESENT relative to embedded P
    (R' = P' = E_matrix). -/
theorem simultaneous_satisfies_present :
    satisfiesTense .present embeddedSickSimultaneous = true := by native_decide

/-- The shifted embedded frame satisfies PAST relative to embedded P
    (R' < P' = E_matrix). -/
theorem shifted_satisfies_past :
    satisfiesTense .past embeddedSickShifted = true := by native_decide

/-- The present-under-past frame satisfies PRESENT relative to embedded P. -/
theorem presentUnderPast_satisfies_present :
    satisfiesTense .present embeddedSickPresent = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Constructor Matching
-- ════════════════════════════════════════════════════════════════

/-- The `simultaneousFrame` constructor reproduces the hand-built
    simultaneous data frame. -/
theorem simultaneousFrame_matches :
    simultaneousFrame matrixSaid (-2) = embeddedSickSimultaneous := by rfl

/-- The `shiftedFrame` constructor reproduces the hand-built
    shifted data frame. -/
theorem shiftedFrame_matches :
    shiftedFrame matrixSaid (-5) (-5) = embeddedSickShifted := by rfl


-- ════════════════════════════════════════════════════════════════
-- § SOT Parameter Bridge
-- ════════════════════════════════════════════════════════════════

/-- English has the simultaneous reading (SOT language). -/
theorem english_simultaneous_available :
    .simultaneous ∈ availableReadings .relative :=
  sot_simultaneous_available

/-- Japanese lacks the simultaneous reading (non-SOT language). -/
theorem japanese_no_simultaneous :
    .simultaneous ∉ availableReadings .absolute :=
  nonSOT_no_simultaneous

/-- Japanese only has the shifted reading. -/
theorem japanese_only_shifted :
    availableReadings .absolute = [.shifted] :=
  nonSOT_only_shifted


-- ════════════════════════════════════════════════════════════════
-- § composeTense Derivation
-- ════════════════════════════════════════════════════════════════

/-- Both readings yield overall past relative to speech time.
    The simultaneous reading's R' = -2 < 0 = S, and the shifted
    reading's R' = -5 < 0 = S. Both are PAST relative to S.
    This matches `composeTense .past .past = .past`. -/
theorem both_readings_overall_past :
    satisfiesTense .past
      { speechTime := (0 : ℤ), perspectiveTime := 0,
        referenceTime := embeddedSickSimultaneous.referenceTime,
        eventTime := embeddedSickSimultaneous.eventTime } = true ∧
    satisfiesTense .past
      { speechTime := (0 : ℤ), perspectiveTime := 0,
        referenceTime := embeddedSickShifted.referenceTime,
        eventTime := embeddedSickShifted.eventTime } = true := by
  constructor <;> native_decide



-- ════════════════════════════════════════════════════════════════
-- § Upper Limit Constraint Bridge (Abusch 1997)
-- ════════════════════════════════════════════════════════════════

/-- Forward-shifted reading violates ULC (Abusch 1997).
    R' = -1 > E_matrix = -2, so R' ≤ E_matrix fails. -/
theorem forwardShifted_violates_ulc :
    ¬ upperLimitConstraint
      embeddedSickForwardShifted.referenceTime
      matrixSaid.eventTime := by native_decide

/-- Simultaneous reading satisfies ULC: R' = E_matrix → R' ≤ E_matrix. -/
theorem simultaneous_satisfies_ulc :
    upperLimitConstraint
      embeddedSickSimultaneous.referenceTime
      matrixSaid.eventTime := by native_decide

/-- Shifted reading satisfies ULC: R' < E_matrix → R' ≤ E_matrix. -/
theorem shifted_satisfies_ulc :
    upperLimitConstraint
      embeddedSickShifted.referenceTime
      matrixSaid.eventTime := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Aspect–Tense Pipeline (relocated from SequenceOfTense.lean)
-- ════════════════════════════════════════════════════════════════

/-!
### Compositional Pipeline: Aspect → Tense

Kratzer (1998) decomposes English simple past as PRES + PERF (present
tense scoping over perfect aspect). The existing `PointPred.toSitProp`
in ViewpointAspect.lean bridges aspect-level PointPred to situation-level
SitProp. The following theorem shows the full pipeline is well-typed:

    EventPred →[PERF∘PRFV]→ PointPred →[toSitProp]→ SitProp →[PAST]→ Prop
-/

open TruthConditional.Sentence.Tense (PAST SitProp)
open TruthConditional.Verb.ViewpointAspect (perfSimple EventPred PointPred)

/-- The compositional pipeline from aspect to tense is well-typed:
    EventPred →[PERF∘PRFV]→ PointPred →[toSitProp]→ SitProp →[PAST]→ Prop.

    This witnesses that the aspect layer feeds into the tense layer
    through the existing type bridge. -/
theorem aspect_tense_pipeline_types {W Time : Type*} [LinearOrder Time]
    (P : EventPred W Time) (s s' : Core.Time.Situation W Time) :
    PAST (perfSimple P).toSitProp s s' ↔
    s.time < s'.time ∧ (perfSimple P) s.world s.time := by
  rfl


-- ════════════════════════════════════════════════════════════════
-- § evalPast ↔ PAST Bridge
-- ════════════════════════════════════════════════════════════════

/-!
### Point-Level ↔ Situation-Level Tense

The aspect pipeline produces `PointPred W Time = W → Time → Prop`, while
tense operators (`PAST`, `PRES`) work on `SitProp = Situation W Time → Prop`.
These theorems prove the two layers compose: `evalPast` (existential past
over point predicates) agrees with `PAST` (situation-level past) via
`PointPred.toSitProp`.
-/

open TruthConditional.Sentence.TenseAspectComposition (evalPast evalPres)

/-- `evalPast` (point-level) agrees with `PAST` (situation-level) via `toSitProp`.

    This connects the two temporal type systems:
    - `evalPast p tc w = ∃ t < tc, p w t` (from TenseAspectComposition)
    - `PAST P s s' = s.time < s'.time ∧ P s` (from Tense.Basic)

    The bridge type `SitProp` (via `toSitProp`) makes them interchangeable. -/
theorem evalPast_iff_PAST {W Time : Type*} [LinearOrder Time]
    (p : PointPred W Time) (tc : Time) (w : W) :
    evalPast p tc w ↔
    ∃ t : Time, PAST p.toSitProp ⟨w, t⟩ ⟨w, tc⟩ := by
  rfl

/-- `evalPres` (point-level) agrees with `toSitProp` at speech time.

    Note: `PRES` adds a `tc = tc` conjunct, so we bridge to `toSitProp`
    directly, which is the cleaner statement. -/
theorem evalPres_iff_toSitProp {W Time : Type*}
    (p : PointPred W Time) (tc : Time) (w : W) :
    evalPres p tc w ↔ p.toSitProp ⟨w, tc⟩ := by
  rfl


-- ════════════════════════════════════════════════════════════════
-- § Reichenbach–Aspect Correspondence
-- ════════════════════════════════════════════════════════════════

/-!
### Data Frames Satisfy Derivation Assumptions

The derivation theorems in `SequenceOfTense.lean` (e.g., `past_under_past_shifted_is_past`)
use hypotheses like `h_perfective : E ≤ R`. These bridge theorems verify that the
concrete data frames in `Data.lean` actually satisfy these assumptions, closing the
loop between stipulative `composeTense` and its derived justification.
-/

/-- The matrix "said" frame is perfective (E = R). -/
theorem matrixSaid_is_perfective :
    matrixSaid.isPerfective := rfl

/-- The shifted embedded frame is perfective (E = R). -/
theorem embeddedShifted_is_perfective :
    embeddedSickShifted.isPerfective := rfl

/-- Perfective aspect (E = R) implies the `E ≤ R` assumption
    used in the derivation theorems. -/
theorem perfective_implies_aspect_assumption
    {Time : Type*} [LinearOrder Time] (f : ReichenbachFrame Time)
    (h : f.isPerfective) : f.eventTime ≤ f.referenceTime :=
  le_of_eq h


end Phenomena.SequenceOfTense.Bridge
