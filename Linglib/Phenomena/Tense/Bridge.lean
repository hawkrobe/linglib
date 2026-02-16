import Linglib.Phenomena.Tense.Data
import Linglib.Theories.Semantics.Tense.Abusch
import Linglib.Theories.Semantics.Tense.VonStechow
import Linglib.Theories.Semantics.Tense.Kratzer
import Linglib.Theories.Semantics.Tense.Ogihara
import Linglib.Theories.Semantics.Tense.Klecha
import Linglib.Theories.Semantics.Tense.Deal
import Linglib.Theories.Semantics.Tense.Sharvit
import Linglib.Theories.Syntax.Minimalism.Tense.Zeijlstra
import Linglib.Theories.Syntax.Minimalism.Tense.Wurmbrand
import Linglib.Theories.Semantics.Tense.TenseAspectComposition
import Linglib.Core.Morphology.Tense
import Linglib.Fragments.English.Tense

/-!
# Tense Phenomena: Bridge Theorems

Per-theory × per-phenomenon derivation theorems connecting the empirical
data in `Data.lean` to the nine tense theories in
`Theories/Semantics.Intensional/Tense/` and `Theories/Minimalism/Tense/`.

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
open Semantics.Tense (satisfiesTense SOTParameter)
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Root-Clause Baseline Verification (§0)
-- ════════════════════════════════════════════════════════════════

-- ── satisfiesTense ──

/-- Simple past satisfies PAST. -/
theorem simplePastLeft_satisfies_past :
    satisfiesTense .past simplePastLeft = true := by native_decide

/-- Simple present satisfies PRESENT. -/
theorem simplePresentRains_satisfies_present :
    satisfiesTense .present simplePresentRains = true := by native_decide

/-- Simple future satisfies FUTURE. -/
theorem simpleFutureWillLeave_satisfies_future :
    satisfiesTense .future simpleFutureWillLeave = true := by native_decide

/-- Simple past does NOT satisfy PRESENT or FUTURE. -/
theorem simplePastLeft_not_present :
    satisfiesTense .present simplePastLeft = false := by native_decide

theorem simplePastLeft_not_future :
    satisfiesTense .future simplePastLeft = false := by native_decide


-- ── GramTense.constrains ↔ isPast / isPresent / isFuture ──

/-- `GramTense.constrains` agrees with `isPast` for simple past. -/
theorem constrains_agrees_isPast :
    GramTense.past.constrains simplePastLeft.referenceTime
      simplePastLeft.perspectiveTime ↔
    simplePastLeft.isPast := Iff.rfl

/-- `GramTense.constrains` agrees with `isPresent` for simple present. -/
theorem constrains_agrees_isPresent :
    GramTense.present.constrains simplePresentRains.referenceTime
      simplePresentRains.perspectiveTime ↔
    simplePresentRains.isPresent := Iff.rfl

/-- `GramTense.constrains` agrees with `isFuture` for simple future. -/
theorem constrains_agrees_isFuture :
    GramTense.future.constrains simpleFutureWillLeave.referenceTime
      simpleFutureWillLeave.perspectiveTime ↔
    simpleFutureWillLeave.isFuture := Iff.rfl


-- ── Morphology: form generation ──

section Morphology
open Core.Morphology.Tense

/-- Past rule generates "walked" from "walk". -/
theorem pastRule_walk : (pastRule Unit).formRule "walk" = "walked" := rfl

/-- Present rule generates "walks" from "walk". -/
theorem presentRule_walk : (presentRule Unit).formRule "walk" = "walks" := rfl

/-- Future rule generates "will leave" from "leave". -/
theorem futureRule_leave : (futureRule Unit).formRule "leave" = "will leave" := rfl

/-- Irregular past form overrides default. -/
theorem pastRule_irregular_went :
    (pastRule Unit (irregularForm := some "went")).formRule "go" = "went" := rfl

/-- Past participle rule generates "walked" from "walk". -/
theorem pastPartRule_walk : (pastPartRule Unit).formRule "walk" = "walked" := rfl

/-- Periphrastic past generates "used to walk". -/
theorem periphPastRule_walk :
    (periphrasticPastRule Unit).formRule "walk" = "used to walk" := rfl

/-- Periphrastic future generates "going to leave". -/
theorem periphFutureRule_leave :
    (periphrasticFutureRule Unit).formRule "leave" = "going to leave" := rfl

/-- All tense rules have `.tense` category. -/
theorem all_tense_category :
    (pastRule Unit).category = .tense ∧
    (presentRule Unit).category = .tense ∧
    (futureRule Unit).category = .tense :=
  ⟨rfl, rfl, rfl⟩

/-- All synthetic tense rules are semantically vacuous —
    temporal semantics comes from the Theory layer, not morphology. -/
theorem all_tense_vacuous :
    (pastRule Unit).isVacuous = true ∧
    (presentRule Unit).isVacuous = true ∧
    (futureRule Unit).isVacuous = true :=
  ⟨rfl, rfl, rfl⟩

end Morphology


-- ── English fragment: tense perspective entries ──

section EnglishFragment
open Fragments.English.Tense

/-- English simple past perspective entry has `gramTense = .past`. -/
theorem eng_simplePast_gramTense :
    simplePastPerspective.gramTense = .past := rfl

/-- English simple present perspective entry has `gramTense = .present`. -/
theorem eng_simplePresent_gramTense :
    simplePresentPerspective.gramTense = .present := rfl

/-- Synthetic forms allow false tense (Lakoff 1970). -/
theorem eng_synthetic_allows_false :
    simplePastPerspective.allowsFalseTense = true ∧
    simplePresentPerspective.allowsFalseTense = true :=
  ⟨rfl, rfl⟩

/-- Periphrastic forms block false tense (Lakoff 1970). -/
theorem eng_periphrastic_blocks_false :
    usedTo.allowsFalseTense = false ∧
    goingTo.allowsFalseTense = false :=
  ⟨rfl, rfl⟩

/-- Simple past is synthetic; "used to" is periphrastic. -/
theorem eng_formType_classification :
    simplePastPerspective.formType = .synthetic ∧
    usedTo.formType = .periphrastic :=
  ⟨rfl, rfl⟩

end EnglishFragment


-- ── TensePronoun: root-clause frame derivation ──

section TensePronounBridge

/-- An indexical past tense pronoun at root level (g maps var 1 to -2,
    P = S = 0) produces a frame satisfying `isPast`. -/
theorem tensePronoun_past_root :
    let tp : TensePronoun := ⟨1, .past, .indexical, 0⟩
    let g : TemporalAssignment ℤ := λ n => if n = 1 then -2 else 0
    let frame := tp.toFrame g 0 0 (-2)
    frame.isPast := by
  simp only [TensePronoun.toFrame, TensePronoun.resolve, ReichenbachFrame.isPast]
  change (-2 : ℤ) < 0; omega

/-- An indexical present tense pronoun at root level produces
    a frame satisfying `isPresent` (R = P). -/
theorem tensePronoun_present_root :
    let tp : TensePronoun := ⟨1, .present, .indexical, 0⟩
    let g : TemporalAssignment ℤ := λ _ => 0
    let frame := tp.toFrame g 0 0 0
    frame.isPresent := by
  simp only [TensePronoun.toFrame, TensePronoun.resolve, ReichenbachFrame.isPresent]
  change (0 : ℤ) = 0; rfl

/-- An indexical future tense pronoun at root level produces
    a frame satisfying `isFuture` (P < R). -/
theorem tensePronoun_future_root :
    let tp : TensePronoun := ⟨1, .future, .indexical, 0⟩
    let g : TemporalAssignment ℤ := λ n => if n = 1 then 3 else 0
    let frame := tp.toFrame g 0 0 3
    frame.isFuture := by
  simp only [TensePronoun.toFrame, TensePronoun.resolve, ReichenbachFrame.isFuture]
  change (0 : ℤ) < 3; omega

/-- The tense pronoun's presupposition matches the frame's tense
    classification: a past tense pronoun presupposes R < P. -/
theorem tensePronoun_presupposition_matches_frame :
    let tp : TensePronoun := ⟨1, .past, .indexical, 0⟩
    tp.presupposition (-2 : ℤ) 0 ↔ simplePastLeft.isPast := Iff.rfl

end TensePronounBridge


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

open Semantics.Tense (PAST SitProp)
open Semantics.Lexical.Verb.ViewpointAspect (perfSimple EventPred PointPred)

/-- The compositional pipeline from aspect to tense is well-typed. -/
theorem aspect_tense_pipeline_types {W Time : Type*} [LinearOrder Time]
    (P : EventPred W Time) (s s' : Core.Time.Situation W Time) :
    PAST (perfSimple P).toSitProp s s' ↔
    s.time < s'.time ∧ (perfSimple P) s.world s.time := by
  rfl


-- ════════════════════════════════════════════════════════════════
-- § evalPast ↔ PAST Bridge
-- ════════════════════════════════════════════════════════════════

open Semantics.TenseAspectComposition (evalPast evalPres)

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

open Semantics.Tense.Abusch

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

open Semantics.Tense.VonStechow

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

open Semantics.Tense.Kratzer

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

open Semantics.Tense.Ogihara

/-- Ogihara derives the simultaneous frame via zero tense. -/
theorem ogihara_derives_embeddedSickSimultaneous
    (g : TemporalAssignment ℤ) (n : ℕ) :
    let embeddedR := zeroTenseSemantics g n matrixSaid.eventTime
    (embeddedFrame matrixSaid embeddedR embeddedR).isPresent := by
  simp [zeroTenseSemantics, embeddedFrame, ReichenbachFrame.isPresent]


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Klecha
-- ════════════════════════════════════════════════════════════════

open Semantics.Tense.Klecha

/-- Klecha derives the modal-past data: past tense checked against
    modal eval time. -/
theorem klecha_derives_modalPast :
    modalPast.isPast := by
  simp only [ReichenbachFrame.isPast, modalPast]; omega


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Deal
-- ════════════════════════════════════════════════════════════════

open Semantics.Tense.Deal

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

open Semantics.Tense.Sharvit

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



-- ════════════════════════════════════════════════════════════════
-- § Declerck: Domain Shift vs Subordination (§23)
-- ════════════════════════════════════════════════════════════════

/-- Both `left` frames satisfy PAST. -/
theorem domainSubordLeft_is_past :
    satisfiesTense .past domainSubordLeft = true := by native_decide

theorem domainShiftLeft_is_past :
    satisfiesTense .past domainShiftLeft = true := by native_decide

/-- Subordination: `wouldReturn` satisfies FUTURE relative to shifted P. -/
theorem domainSubordWouldReturn_is_future :
    satisfiesTense .future domainSubordWouldReturn = true := by native_decide

/-- Shift: `cameBack` satisfies PAST relative to absolute P. -/
theorem domainShiftCameBack_is_past :
    satisfiesTense .past domainShiftCameBack = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Declerck: False Tense (§24)
-- ════════════════════════════════════════════════════════════════

/-- Both false-past frames satisfy PRESENT (despite past morphology). -/
theorem falsePastWanted_satisfies_present :
    satisfiesTense .present falsePastWanted = true := by native_decide

theorem falsePastCould_satisfies_present :
    satisfiesTense .present falsePastCould = true := by native_decide

/-- False tense and fake past produce identical frames:
    the distinction is pragmatic (politeness vs counterfactuality),
    not temporal-structural. -/
theorem falsePast_counterfactual_same_frame :
    falsePastWanted = counterfactualWere := rfl


-- ════════════════════════════════════════════════════════════════
-- § Declerck: PPS vs FPS in Conditionals (§25)
-- ════════════════════════════════════════════════════════════════

/-- PPS if-clause satisfies PRESENT. -/
theorem pps_ifClause_satisfies_present :
    satisfiesTense .present ppsIfComes = true := by native_decide

/-- FPS if-clause satisfies FUTURE. -/
theorem fps_ifClause_satisfies_future :
    satisfiesTense .future fpsIfWillGo = true := by native_decide

/-- PPS matrix satisfies FUTURE. -/
theorem pps_matrix_satisfies_future :
    satisfiesTense .future ppsWillBeHappy = true := by native_decide

/-- FPS matrix satisfies PRESENT. -/
theorem fps_matrix_satisfies_present :
    satisfiesTense .present fpsShouldPublish = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Declerck: Temporal Conjunctions (§26)
-- ════════════════════════════════════════════════════════════════

/-- Future perfect satisfies FUTURE (R > P). -/
theorem futPerfLeft_satisfies_future :
    satisfiesTense .future futPerfLeft = true := by native_decide

/-- When-clause satisfies PRESENT relative to implicit TO. -/
theorem whenArrives_satisfies_present :
    satisfiesTense .present whenArrives = true := by native_decide

/-- Past perfect satisfies PAST (R < P). -/
theorem hadLeftBefore_satisfies_past :
    satisfiesTense .past hadLeftBefore = true := by native_decide

/-- Before-clause satisfies PAST. -/
theorem beforeArrived_satisfies_past :
    satisfiesTense .past beforeArrived = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Declerck: Bounded/Unbounded (§27)
-- ════════════════════════════════════════════════════════════════

/-- All §27 frames satisfy PAST. -/
theorem arrivedBounded_satisfies_past :
    satisfiesTense .past arrivedBounded.frame = true := by native_decide

theorem satDownBounded_satisfies_past :
    satisfiesTense .past satDownBounded.frame = true := by native_decide

theorem rainingUnbounded_satisfies_past :
    satisfiesTense .past rainingUnbounded.frame = true := by native_decide

theorem windBlowingUnbounded_satisfies_past :
    satisfiesTense .past windBlowingUnbounded.frame = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Declerck: Present Perfect vs Preterit (§28)
-- ════════════════════════════════════════════════════════════════

/-- Present perfect satisfies PRESENT (R = P: present time-sphere). -/
theorem perfectVisitedParis_satisfies_present :
    satisfiesTense .present perfectVisitedParis = true := by native_decide

/-- Preterit satisfies PAST (R < P: past time-sphere). -/
theorem preteritVisitedParis_satisfies_past :
    satisfiesTense .past preteritVisitedParis = true := by native_decide

/-- Both time-sphere frames have identical event time:
    the structural difference is R's relation to P, not E's location. -/
theorem perfectPreterit_same_eventTime :
    perfectVisitedParis.eventTime = preteritVisitedParis.eventTime := rfl


end Phenomena.Tense.Bridge
