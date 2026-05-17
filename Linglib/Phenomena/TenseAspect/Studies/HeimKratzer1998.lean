import Linglib.Phenomena.TenseAspect.Studies.HeimKratzer1998Data
import Linglib.Theories.Semantics.Tense.SOT.Decomposition
import Linglib.Theories.Semantics.Tense.Modal.Matrix
import Linglib.Theories.Semantics.Tense.Counterfactual.Defs
import Linglib.Theories.Syntax.Minimalist.Tense.AgreeSOT
import Linglib.Theories.Syntax.Minimalist.Tense.InfinitivalTense
import Linglib.Theories.Semantics.Tense.TenseAspectComposition
import Linglib.Core.Morphology.Exponence
import Linglib.Fragments.English.Tense

/-!
# Tense Phenomena: Bridge Theorems
@cite{lakoff-1970}

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

-/

namespace Phenomena.TenseAspect.Bridge

open Core.Time.Reichenbach
open Core.Time.Tense
open Phenomena.TenseAspect
open Semantics.Tense


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
    (pastRule Unit).delegatedSemantics = true ∧
    (presentRule Unit).delegatedSemantics = true ∧
    (futureRule Unit).delegatedSemantics = true :=
  ⟨rfl, rfl, rfl⟩

end Morphology


-- ── English fragment: tense perspective entries ──

section EnglishFragment
open Fragments.English.Tense

/-- English simple past perspective entry has `gramTense =.past`. -/
theorem eng_simplePast_gramTense :
    simplePastPerspective.gramTense = .past := rfl

/-- English simple present perspective entry has `gramTense =.present`. -/
theorem eng_simplePresent_gramTense :
    simplePresentPerspective.gramTense = .present := rfl

/-- Synthetic forms allow false tense. -/
theorem eng_synthetic_allows_false :
    simplePastPerspective.allowsFalseTense = true ∧
    simplePresentPerspective.allowsFalseTense = true :=
  ⟨rfl, rfl⟩

/-- Periphrastic forms block false tense. -/
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

/-- An indexical future tense pronoun at root level produces
    a frame satisfying `isFuture` (P < R). -/
theorem tensePronoun_future_root :
    let tp : TensePronoun := ⟨1, .future, .indexical, 0⟩
    let g : TemporalAssignment ℤ := λ n => if n = 1 then 3 else 0
    let frame := tp.toFrame g 0 0 3
    frame.isFuture := by
  simp only [TensePronoun.toFrame, TensePronoun.resolve, ReichenbachFrame.isFuture]
  change (0 : ℤ) < 3; omega

end TensePronounBridge


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
-- § Aspect-Tense Pipeline
-- ════════════════════════════════════════════════════════════════

open Semantics.Tense (PAST SitProp)
open Semantics.Events (EventPred)
open Semantics.Aspect.Core (perfSimple PointPred)

/-- The compositional pipeline from aspect to tense is well-typed. -/
theorem aspect_tense_pipeline_types {W Time : Type*} [LinearOrder Time]
    (P : EventPred W Time) (s s' : Core.WorldTimeIndex W Time) :
    PAST (perfSimple P) s s' ↔
    s.time < s'.time ∧ (perfSimple P) s := by
  rfl


-- ════════════════════════════════════════════════════════════════
-- § evalPast ↔ PAST Bridge
-- ════════════════════════════════════════════════════════════════

open Semantics.Tense.TenseAspectComposition (evalPast evalPres)

/-- `evalPast` agrees with `PAST`. -/
theorem evalPast_iff_PAST {W Time : Type*} [LinearOrder Time]
    (p : PointPred W Time) (tc : Time) (w : W) :
    evalPast p tc w ↔
    ∃ t : Time, PAST p ⟨w, t⟩ ⟨w, tc⟩ := by
  rfl

/-- `evalPres` agrees with `PointPred` application at speech time. -/
theorem evalPres_iff_toSitProp {W Time : Type*}
    (p : PointPred W Time) (tc : Time) (w : W) :
    evalPres p tc w ↔ p ⟨w, tc⟩ := by
  rfl


-- ════════════════════════════════════════════════════════════════
-- § Per-Theory Derivations: Sharvit
-- ════════════════════════════════════════════════════════════════

-- (§23-28 satisfiesTense theorems deleted: vacuous unfoldings of frame definitions;
--  the frames themselves migrated to Studies/Declerck1991.lean and the bridge bridges
--  nothing — `satisfiesTense .past f` reduces by `decide` directly for any concrete f.)


end Phenomena.TenseAspect.Bridge
