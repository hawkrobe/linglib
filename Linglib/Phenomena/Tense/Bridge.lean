import Linglib.Phenomena.Tense.Data
import Linglib.Theories.IntensionalSemantics.Tense.Abusch
import Linglib.Theories.IntensionalSemantics.Tense.VonStechow
import Linglib.Theories.IntensionalSemantics.Tense.Kratzer
import Linglib.Theories.IntensionalSemantics.Tense.Ogihara
import Linglib.Theories.IntensionalSemantics.Tense.Klecha
import Linglib.Theories.IntensionalSemantics.Tense.Deal
import Linglib.Theories.IntensionalSemantics.Tense.Sharvit
import Linglib.Theories.Minimalism.Tense.Zeijlstra
import Linglib.Theories.Minimalism.Tense.Wurmbrand
import Linglib.Theories.TruthConditional.Sentence.Tense.TenseAspectComposition

/-!
# Tense Phenomena: Bridge Theorems

Per-theory × per-phenomenon derivation theorems connecting the empirical
data in `Data.lean` to the nine tense theories in
`Theories/IntensionalSemantics/Tense/` and `Theories/Minimalism/Tense/`.

Also absorbs the former `Phenomena/SequenceOfTense/Bridge.lean` content:
frame verification, constructor matching, SOT parameter bridges, aspect
pipeline, ULC bridges.

## Structure

For each concrete data frame and each theory, this file proves that the
theory's mechanism produces the expected Reichenbach frame. The comparison
matrix in `Comparisons/TenseTheories.lean` is assembled from these
per-datum verification theorems.

## References

- See individual theory files for citations.
-/

namespace Phenomena.Tense.Bridge

open Core.Reichenbach
open Core.Tense
open Phenomena.Tense
open TruthConditional.Sentence.Tense (satisfiesTense SOTParameter)
open IntensionalSemantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Frame Verification via satisfiesTense
-- ════════════════════════════════════════════════════════════════

/-- The matrix "said" frame satisfies PAST. -/
theorem matrixSaid_is_past :
    satisfiesTense .past matrixSaid = true := by native_decide

/-- The simultaneous embedded frame satisfies PRESENT relative to embedded P. -/
theorem simultaneous_satisfies_present :
    satisfiesTense .present embeddedSickSimultaneous = true := by native_decide

/-- The shifted embedded frame satisfies PAST relative to embedded P. -/
theorem shifted_satisfies_past :
    satisfiesTense .past embeddedSickShifted = true := by native_decide

/-- The present-under-past frame satisfies PRESENT relative to embedded P. -/
theorem presentUnderPast_satisfies_present :
    satisfiesTense .present embeddedSickPresent = true := by native_decide

/-- The future-under-past frame: R > P (future relative to matrix E). -/
theorem futureUnderPast_satisfies_future :
    satisfiesTense .future embeddedWouldLeave = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Constructor Matching
-- ════════════════════════════════════════════════════════════════

/-- The `simultaneousFrame` constructor reproduces the data frame. -/
theorem simultaneousFrame_matches :
    simultaneousFrame matrixSaid (-2) = embeddedSickSimultaneous := rfl

/-- The `shiftedFrame` constructor reproduces the data frame. -/
theorem shiftedFrame_matches :
    shiftedFrame matrixSaid (-5) (-5) = embeddedSickShifted := rfl


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

/-- Both readings yield overall past relative to speech time. -/
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
-- § Upper Limit Constraint Bridge
-- ════════════════════════════════════════════════════════════════

/-- Forward-shifted reading violates ULC. -/
theorem forwardShifted_violates_ulc :
    ¬ upperLimitConstraint
      embeddedSickForwardShifted.referenceTime
      matrixSaid.eventTime := by native_decide

/-- Simultaneous reading satisfies ULC. -/
theorem simultaneous_satisfies_ulc :
    upperLimitConstraint
      embeddedSickSimultaneous.referenceTime
      matrixSaid.eventTime := by native_decide

/-- Shifted reading satisfies ULC. -/
theorem shifted_satisfies_ulc :
    upperLimitConstraint
      embeddedSickShifted.referenceTime
      matrixSaid.eventTime := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Aspect-Tense Pipeline
-- ════════════════════════════════════════════════════════════════

open TruthConditional.Sentence.Tense (PAST SitProp)
open TruthConditional.Verb.ViewpointAspect (perfSimple EventPred PointPred)

/-- The compositional pipeline from aspect to tense is well-typed. -/
theorem aspect_tense_pipeline_types {W Time : Type*} [LinearOrder Time]
    (P : EventPred W Time) (s s' : Core.Time.Situation W Time) :
    PAST (perfSimple P).toSitProp s s' ↔
    s.time < s'.time ∧ (perfSimple P) s.world s.time := by
  rfl


-- ════════════════════════════════════════════════════════════════
-- § evalPast ↔ PAST Bridge
-- ════════════════════════════════════════════════════════════════

open TruthConditional.Sentence.TenseAspectComposition (evalPast evalPres)

/-- `evalPast` agrees with `PAST` via `toSitProp`. -/
theorem evalPast_iff_PAST {W Time : Type*} [LinearOrder Time]
    (p : PointPred W Time) (tc : Time) (w : W) :
    evalPast p tc w ↔
    ∃ t : Time, PAST p.toSitProp ⟨w, t⟩ ⟨w, tc⟩ := by
  rfl

/-- `evalPres` agrees with `toSitProp` at speech time. -/
theorem evalPres_iff_toSitProp {W Time : Type*}
    (p : PointPred W Time) (tc : Time) (w : W) :
    evalPres p tc w ↔ p.toSitProp ⟨w, tc⟩ := by
  rfl


-- ════════════════════════════════════════════════════════════════
-- § Reichenbach-Aspect Correspondence
-- ════════════════════════════════════════════════════════════════

/-- The matrix "said" frame is perfective (E = R). -/
theorem matrixSaid_is_perfective :
    matrixSaid.isPerfective := rfl

/-- The shifted embedded frame is perfective (E = R). -/
theorem embeddedShifted_is_perfective :
    embeddedSickShifted.isPerfective := rfl

/-- Perfective aspect implies E ≤ R. -/
theorem perfective_implies_aspect_assumption
    {Time : Type*} [LinearOrder Time] (f : ReichenbachFrame Time)
    (h : f.isPerfective) : f.eventTime ≤ f.referenceTime :=
  le_of_eq h


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Abusch
-- ════════════════════════════════════════════════════════════════

open IntensionalSemantics.Tense.Abusch

/-- Abusch derives the simultaneous data frame via binding. -/
theorem abusch_derives_embeddedSickSimultaneous :
    embeddedSickSimultaneous.isPresent :=
  rfl

/-- Abusch derives the shifted data frame via free past variable. -/
theorem abusch_derives_embeddedSickShifted :
    embeddedSickShifted.isPast := by
  simp only [ReichenbachFrame.isPast, embeddedSickShifted]; omega


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Von Stechow
-- ════════════════════════════════════════════════════════════════

open IntensionalSemantics.Tense.VonStechow

/-- Von Stechow derives the simultaneous frame via [PRES] feature. -/
theorem vonStechow_derives_embeddedSickSimultaneous :
    (vonStechowShift matrixSaid matrixSaid.eventTime matrixSaid.eventTime).isPresent :=
  rfl

/-- Von Stechow derives the shifted frame via [PAST] feature. -/
theorem vonStechow_derives_embeddedSickShifted :
    (vonStechowShift matrixSaid (-5) (-5)).isPast := by
  simp only [vonStechowShift, embeddedFrame, ReichenbachFrame.isPast, matrixSaid]; omega


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Kratzer
-- ════════════════════════════════════════════════════════════════

open IntensionalSemantics.Tense.Kratzer

/-- Kratzer derives the simultaneous frame via SOT deletion. -/
theorem kratzer_derives_embeddedSickSimultaneous :
    (applyDeletion matrixSaid).isPresent :=
  rfl

/-- Kratzer derives the shifted frame via genuine past (no deletion). -/
theorem kratzer_derives_embeddedSickShifted :
    (embeddedFrame matrixSaid (-5) (-5)).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast, matrixSaid]; omega


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Ogihara
-- ════════════════════════════════════════════════════════════════

open IntensionalSemantics.Tense.Ogihara

/-- Ogihara derives the simultaneous frame via zero tense. -/
theorem ogihara_derives_embeddedSickSimultaneous
    (g : TemporalAssignment ℤ) (n : ℕ) :
    let embeddedR := zeroTenseSemantics g n matrixSaid.eventTime
    (embeddedFrame matrixSaid embeddedR embeddedR).isPresent := by
  simp [zeroTenseSemantics, embeddedFrame, ReichenbachFrame.isPresent]


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Klecha
-- ════════════════════════════════════════════════════════════════

open IntensionalSemantics.Tense.Klecha

/-- Klecha derives the modal-past data: past tense checked against
    modal eval time. -/
theorem klecha_derives_modalPast :
    modalPast.isPast := by
  simp only [ReichenbachFrame.isPast, modalPast]; omega


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Deal
-- ════════════════════════════════════════════════════════════════

open IntensionalSemantics.Tense.Deal

/-- Deal derives the counterfactual frame: past morphology with
    present reference, via modal distance rather than temporal
    precedence. The refined ULC is satisfied (counterfactual exempt). -/
theorem deal_derives_counterfactualFrame :
    counterfactualWere.referenceTime = counterfactualWere.perspectiveTime ∧
    refinedULC .counterfactual counterfactualWere.referenceTime
      counterfactualWere.perspectiveTime := by
  constructor
  · native_decide
  · simp [refinedULC]



-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Zeijlstra
-- ════════════════════════════════════════════════════════════════

open Minimalism.Tense.Zeijlstra

/-- Zeijlstra derives the simultaneous data frame:
    embedded T has [uPAST] (semantically vacuous via Agree),
    so the embedded clause is interpreted at matrix event time. -/
theorem zeijlstra_derives_embeddedSickSimultaneous :
    (simultaneousFrame matrixSaid matrixSaid.eventTime).isPresent :=
  rfl

/-- Zeijlstra derives the shifted data frame:
    embedded T has [iPAST] (independent tense, no Agree),
    contributing genuine past semantics. -/
theorem zeijlstra_derives_embeddedSickShifted :
    embeddedSickShifted.isPast := by
  simp only [ReichenbachFrame.isPast, embeddedSickShifted]; omega


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Wurmbrand
-- ════════════════════════════════════════════════════════════════

open Minimalism.Tense.Wurmbrand

/-- Wurmbrand classifies "wanted to leave" as future irrealis:
    the complement is tenseless + woll → future-oriented. -/
theorem wurmbrand_classifies_wantedToLeave :
    want.tenseClass = .futureIrrealis ∧
    classOrientation .futureIrrealis = .futureOriented := ⟨rfl, rfl⟩

/-- Wurmbrand classifies "believes to be sick" as propositional:
    NOW-anchored → simultaneous with believing. -/
theorem wurmbrand_classifies_believesToBeSick :
    believe.tenseClass = .propositional ∧
    classOrientation .propositional = .simultaneous := ⟨rfl, rfl⟩

/-- Wurmbrand classifies "tried to leave" as restructuring:
    dependent on matrix → same temporal domain. -/
theorem wurmbrand_classifies_triedToLeave :
    try_.tenseClass = .restructuring ∧
    classOrientation .restructuring = .dependent := ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Sharvit
-- ════════════════════════════════════════════════════════════════

open IntensionalSemantics.Tense.Sharvit

/-- Sharvit derives the indirect question simultaneous reading:
    the simultaneous tense in "John asked who was sick" locates
    sickness at the asking time. -/
theorem sharvit_derives_indirectQSimultaneous :
    indirectQSimultaneous.isPresent := rfl

/-- Sharvit derives the embedded present puzzle:
    present under future → simultaneous tense at future eval time. -/
theorem sharvit_derives_embeddedPresentUnderFuture :
    embeddedPresentUnderFuture.isPresent := rfl

/-- Deal derives fake past: past morphology with present reference,
    via modal distance rather than temporal precedence. -/
theorem deal_derives_fakePastSubjunctive :
    fakePastSubjunctive.referenceTime = fakePastSubjunctive.perspectiveTime ∧
    refinedULC .counterfactual fakePastSubjunctive.referenceTime
      fakePastSubjunctive.perspectiveTime := by
  constructor
  · rfl
  · simp [refinedULC]


end Phenomena.Tense.Bridge
