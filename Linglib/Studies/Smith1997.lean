import Linglib.Features.Aktionsart
import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Aspect.Composition
import Linglib.Features.Aktionsart
import Linglib.Fragments.English.TenseAspect
import Linglib.Fragments.Romance.French.TenseAspect
import Linglib.Fragments.Mandarin.TenseAspect
import Linglib.Features.MassCount

/-!
# The parameter of aspect

Formalises [smith-1997]'s two-component theory: aspectual meaning factors into
a situation type (`VendlerClass`) and a viewpoint (`ViewpointType`), freely
combinable.

The four visibility properties Smith tabulates for viewpoints (§4.1) are not
restated here as a stipulated lookup — they live in `Semantics/Aspect/Basic.lean`
as `Prop`-valued predicates derived from the TT–TSit interval relation
`ViewpointType.ttTSitRelation`. Smith's Table 1 then re-emerges as the four
substrate iff theorems (`showsInitialPoint_iff`, etc.); this file only
re-packages those into the row-wise groupings Smith uses prose-side.

## Main declarations

* `Smith1997.perfective_closed`, `imperfective_open`, `neutral_intermediate`:
  the row-wise visibility groupings Smith presents in §4.1.
* `Smith1997.AspectualInterpretation`: situation-type × viewpoint pairs.
* `Smith1997.AspectualSystem`, `english`, `french`, `mandarin`, `navajo`:
  per-language viewpoint inventories ([smith-1997] §4.2).
* `Smith1997.ImperfectiveParadoxArises`: the imperfective-paradox locus.
* `Smith1997.PerfectiveEffect`, `Smith1997.perfectiveEffect`: completion vs
  termination under perfective ([smith-1997] §3, pp. 67–68).

## Implementation notes

`VendlerClass`, `Telicity`, and the project's project-canonical
`VendlerClass.HasInternalStages` live in `Features/Aktionsart.lean`.
`ViewpointType` and its derived visibility predicates live in
`Semantics/Aspect/Basic.lean`. Compositional rules (`composeWithNP`,
`overrideTelicity`) live in `Semantics/Aspect/Composition.lean`.

## References

* [smith-1997] Smith, *The Parameter of Aspect* (2nd ed., 1997).
-/

open Features
open Semantics.Aspect (ViewpointType)
open Semantics.Aspect.Composition
open Features (DiagnosticResult)

namespace Smith1997

/-! ### Visibility ([smith-1997] §4.1 Table 1) — row-wise groupings -/

/-- Perfective makes both endpoints visible and presents the situation as closed
    ([smith-1997] §4.1, Table 1). -/
theorem perfective_closed :
    ViewpointType.perfective.ShowsInitialPoint ∧
    ViewpointType.perfective.ShowsFinalPoint ∧
    ViewpointType.perfective.IsClosed :=
  ⟨(ViewpointType.showsInitialPoint_iff _).mpr (Or.inl rfl),
   (ViewpointType.showsFinalPoint_iff _).mpr rfl,
   (ViewpointType.isClosed_iff _).mpr (Or.inl rfl)⟩

/-- Imperfective makes neither endpoint visible and is not closed
    ([smith-1997] §4.1, Table 1). -/
theorem imperfective_open :
    ¬ ViewpointType.imperfective.ShowsInitialPoint ∧
    ¬ ViewpointType.imperfective.ShowsFinalPoint ∧
    ¬ ViewpointType.imperfective.IsClosed := by
  rw [ViewpointType.showsInitialPoint_iff, ViewpointType.showsFinalPoint_iff,
      ViewpointType.isClosed_iff]
  decide

/-- Neutral is intermediate: initial point visible (like perfective), final
    point not asserted (like imperfective), not closed
    ([smith-1997] §4.2.3, p. 80). -/
theorem neutral_intermediate :
    ViewpointType.neutral.ShowsInitialPoint ∧
    ¬ ViewpointType.neutral.ShowsFinalPoint ∧
    ¬ ViewpointType.neutral.IsClosed := by
  refine ⟨?_, ?_, ?_⟩
  · exact (ViewpointType.showsInitialPoint_iff _).mpr (Or.inr rfl)
  · rw [ViewpointType.showsFinalPoint_iff]; decide
  · rw [ViewpointType.isClosed_iff]; decide

/-- Only the imperfective focuses preliminary stages; neutral does not — the
    discriminator between neutral and imperfective ([smith-1997] §4.2.3,
    p. 80, ex. 41). -/
theorem neutral_no_preliminary_stages :
    ¬ ViewpointType.neutral.FocusesPreliminaryStages ∧
    ViewpointType.imperfective.FocusesPreliminaryStages := by
  refine ⟨?_, ?_⟩
  · rw [ViewpointType.focusesPreliminaryStages_iff]; decide
  · exact (ViewpointType.focusesPreliminaryStages_iff _).mpr rfl

/-- Neutral's initial-point visibility matches perfective's (both hold), while
    its final-point visibility matches imperfective's (both fail). -/
theorem neutral_between_perf_imperf :
    (ViewpointType.neutral.ShowsInitialPoint ↔
        ViewpointType.perfective.ShowsInitialPoint) ∧
    (ViewpointType.neutral.ShowsFinalPoint ↔
        ViewpointType.imperfective.ShowsFinalPoint) :=
  ⟨iff_of_true neutral_intermediate.1 perfective_closed.1,
   iff_of_false neutral_intermediate.2.1 imperfective_open.2.1⟩

/-! ### Independence of situation type and viewpoint ([smith-1997] §4.3) -/

/-- An aspectual interpretation: situation type × viewpoint. The two components
    are independent — every cell of the 5 × 5 product is well-formed. -/
structure AspectualInterpretation where
  situationType : VendlerClass
  viewpoint : ViewpointType
  deriving DecidableEq, Repr

/-- Enumeration of all 5 Vendler classes. -/
def allSituationTypes : List VendlerClass :=
  [.state, .activity, .achievement, .accomplishment, .semelfactive]

/-- Enumeration of all 5 viewpoint types. -/
def allViewpoints : List ViewpointType :=
  [.perfective, .imperfective, .neutral, .perfect, .prospective]

/-- All 5 × 5 = 25 aspectual interpretations. -/
def allInterpretations : List AspectualInterpretation :=
  allSituationTypes.flatMap fun st => allViewpoints.map (⟨st, ·⟩)

theorem allInterpretations_length : allInterpretations.length = 25 := by decide

theorem allInterpretations_nodup : allInterpretations.Nodup := by decide

/-! ### Cross-linguistic viewpoint inventories ([smith-1997] §4.2) -/

/-- How the perfective interacts with statives ([smith-1997] pp. 69–70): three
    cross-linguistic patterns. -/
inductive PerfStativeParam where
  /-- Perfective covers statives with a closed interpretation (French
      "Marie a vécu à Paris" asserts the situation is over). -/
  | closed
  /-- Perfective appears with statives, allowing both open and closed
      readings (English "Jennifer knew Turkish"). -/
  | open
  /-- Perfective does not apply to statives (Russian, Chinese, Navajo). -/
  | excluded
  deriving DecidableEq, Repr

/-- A language's aspectual system: which viewpoints are available, which is
    the default, and how the perfective interacts with statives. -/
structure AspectualSystem where
  /-- Language name. -/
  language : String
  /-- Available viewpoint types in this language. -/
  viewpoints : List ViewpointType
  /-- Default viewpoint for aspectually vague sentences. -/
  defaultViewpoint : ViewpointType
  /-- How the perfective interacts with statives. -/
  perfStativeParam : PerfStativeParam
  deriving Repr

/-- English: perfective + imperfective (progressive); no neutral
    ([smith-1997] p. 70). -/
def english : AspectualSystem where
  language := "English"
  viewpoints := [.perfective, .imperfective]
  defaultViewpoint := .perfective
  perfStativeParam := .open

/-- French: perfective + imperfective + neutral (Futur); perfective covers
    statives with closed reading ([smith-1997] p. 70). -/
def french : AspectualSystem where
  language := "French"
  viewpoints := [.perfective, .imperfective, .neutral]
  defaultViewpoint := .perfective
  perfStativeParam := .closed

/-- Mandarin: perfective (-le) + imperfective (zai, -zhe) + neutral (bare);
    perfective excludes statives. -/
def mandarin : AspectualSystem where
  language := "Mandarin"
  viewpoints := [.perfective, .imperfective, .neutral]
  defaultViewpoint := .neutral
  perfStativeParam := .excluded

/-- Navajo: perfective + imperfective + neutral (Usitative/Iterative);
    perfective excludes statives. -/
def navajo : AspectualSystem where
  language := "Navajo"
  viewpoints := [.perfective, .imperfective, .neutral]
  defaultViewpoint := .neutral
  perfStativeParam := .excluded

/-- All four sampled languages have at least perfective and imperfective. -/
theorem universal_core :
    ∀ sys ∈ [english, french, mandarin, navajo],
      ViewpointType.perfective ∈ sys.viewpoints ∧
      ViewpointType.imperfective ∈ sys.viewpoints := by decide

/-- The neutral viewpoint appears in LVM (low-verbal-morphology) languages. -/
theorem neutral_in_lvm_languages :
    ViewpointType.neutral ∈ french.viewpoints ∧
    ViewpointType.neutral ∈ mandarin.viewpoints ∧
    ViewpointType.neutral ∈ navajo.viewpoints := by decide

/-- English lacks the neutral viewpoint. -/
theorem english_no_neutral : ViewpointType.neutral ∉ english.viewpoints := by decide

/-- The three perfective–stative patterns are all attested across the sample. -/
theorem three_perf_stative_patterns :
    english.perfStativeParam = .open ∧
    french.perfStativeParam = .closed ∧
    mandarin.perfStativeParam = .excluded ∧
    navajo.perfStativeParam = .excluded := by decide

/-! ### WALS typology bridge -/

/-- Smith's sample languages all have grammaticalised aspect in WALS Ch. 65.
    Consistent with each having both `.perfective` and `.imperfective`. -/
theorem smith_languages_have_wals_aspect :
    English.tenseAspectProfile.aspect = .grammatical ∧
    French.tenseAspectProfile.aspect = .grammatical ∧
    Mandarin.tenseAspectProfile.aspect = .grammatical := by decide

/-- French has the neutral viewpoint (the Futur), and WALS records French as
    having an inflectional future — consistent across the two encodings. -/
theorem french_neutral_has_inflectional_future :
    ViewpointType.neutral ∈ french.viewpoints ∧
    French.tenseAspectProfile.future = .inflectional := by decide

/-! ### Imperfective paradox -/

/-- The imperfective paradox: imperfective + telic does not entail the
    perfective completion ("Mary was building a house" ⊭ "Mary built a
    house"). The paradox does not arise for atelic situations because their
    subinterval property makes IMPF entail PRFV. -/
def ImperfectiveParadoxArises (ai : AspectualInterpretation) : Prop :=
  ai.viewpoint = .imperfective ∧ ai.situationType.telicity = .telic

instance : DecidablePred ImperfectiveParadoxArises :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem paradox_impf_accomplishment :
    ImperfectiveParadoxArises ⟨.accomplishment, .imperfective⟩ := by decide

theorem not_paradox_impf_activity :
    ¬ ImperfectiveParadoxArises ⟨.activity, .imperfective⟩ := by decide

theorem not_paradox_perfective (c : VendlerClass) :
    ¬ ImperfectiveParadoxArises ⟨c, .perfective⟩ := by
  rintro ⟨h, _⟩
  exact ViewpointType.noConfusion h

/-! ### Perfective effect: completion vs termination ([smith-1997] pp. 67–68) -/

/-- Whether the perfective conveys completion (telic) or termination (atelic),
    or has no effect (non-perfective viewpoints). -/
inductive PerfectiveEffect where
  /-- Natural endpoint reached. -/
  | completion
  /-- Event stopped without reaching a natural endpoint. -/
  | termination
  /-- Not perfective; no completion/termination asserted. -/
  | noEffect
  deriving DecidableEq, Repr

/-- The perfective effect of an aspectual interpretation:
    perfective + telic → completion; perfective + atelic → termination;
    non-perfective viewpoints → no effect. -/
def perfectiveEffect (ai : AspectualInterpretation) : PerfectiveEffect :=
  match ai.viewpoint with
  | .perfective =>
    if ai.situationType.telicity = .telic then .completion else .termination
  | _ => .noEffect

theorem perf_accomplishment_completes :
    perfectiveEffect ⟨.accomplishment, .perfective⟩ = .completion := by decide

theorem perf_activity_terminates :
    perfectiveEffect ⟨.activity, .perfective⟩ = .termination := by decide

theorem perf_achievement_completes :
    perfectiveEffect ⟨.achievement, .perfective⟩ = .completion := by decide

theorem impf_no_completion_termination (c : VendlerClass) :
    perfectiveEffect ⟨c, .imperfective⟩ = .noEffect := rfl

theorem completion_iff_telic (c : VendlerClass) :
    perfectiveEffect ⟨c, .perfective⟩ = .completion ↔ c.telicity = .telic := by
  cases c <;> decide

/-! ### Progressive requires internal stages -/

/-- The progressive accepts exactly the dynamic-durative classes — i.e.
    those with internal stages ([smith-1997] Ch. 4). Smith's claim factored
    through the substrate's `VendlerClass.HasInternalStages`. -/
theorem progressive_requires_HasInternalStages (c : VendlerClass) :
    Features.progressivePrediction c = .accept ↔
    c.HasInternalStages := by
  cases c <;> decide

/-! ### Compositional rule verification ([smith-1997] §3.2.5, §3.3) -/

/-- Smith's external override (§3.2.5) is final — it absorbs all prior
    compositional steps. -/
theorem external_override_is_final (v : AspectualProfile) (np : MassCount)
    (ext : Telicity) :
    (overrideTelicity (composeWithNP v np) ext).telicity = ext := rfl

/-- Smith and [krifka-1989] agree on count/mass NP composition: telic+count
    stays telic, telic+mass atelicises. -/
theorem krifka_smith_agreement :
    (composeWithNP accomplishmentProfile .count).telicity = .telic ∧
    (composeWithNP accomplishmentProfile .mass).telicity = .atelic :=
  ⟨rfl, rfl⟩

/-- Semelfactive duration-coercion gives an activity by three independent
    routes: profile-level `duratize`, feature-level `overrideDuration`, and
    diagnostic-level coercion. -/
theorem semelfactive_coercion_three_ways :
    semelfactiveProfile.duratize.toVendlerClass = .activity ∧
    (overrideDuration semelfactiveProfile .durative).toVendlerClass = .activity ∧
    Features.forXPrediction .semelfactive = .coerced :=
  ⟨rfl, rfl, rfl⟩

/-! ### Bridge to [krifka-1989] -/

/-- Smith's telicity matches Krifka's mereological quantization: a Vendler
    class is telic iff its telicity tag is the quantized `MereoTag.qua`. -/
theorem telic_iff_toMereoTag_qua (c : VendlerClass) :
    c.telicity = .telic ↔ c.telicity.toMereoTag = Core.Order.MereoTag.qua := by
  cases c <;> decide

end Smith1997
