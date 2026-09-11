import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Aspect.Composition
import Linglib.Data.WALS.Features.F65A
import Linglib.Data.WALS.Features.F67A
import Linglib.Features.MassCount

/-!
# The parameter of aspect

Formalises [smith-1997]'s two-component theory: aspectual meaning factors into
a situation type (`VendlerClass`) and a viewpoint (`ViewpointType`), freely
combinable.

The four visibility properties Smith tabulates for viewpoints (§4.1) are not
restated as a stipulated lookup: they are `Prop`-valued predicates derived from the substrate's
TT–TSit interval relation `ViewpointType.ttTSitRelation`, and Smith's Table 1 re-emerges as
four iff theorems (`showsInitialPoint_iff`, etc.), regrouped row-wise below.

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

`VendlerClass`, `Telicity` and `ViewpointType` live in `Semantics/Aspect/Basic.lean`;
compositional rules (`composeWithNP`, `overrideTelicity`) in
`Semantics/Aspect/Composition.lean`; the visibility predicates and `HasInternalStages` are this
file's.

## References

* [smith-1997] Smith, *The Parameter of Aspect* (2nd ed., 1997).
-/

open Aspect Aspect.Composition
namespace Smith1997

/-! ### Visibility

The four visibility properties Table 1 of Section 4.1 tabulates per viewpoint, whether the
initial and the final point of the situation are asserted, whether the viewpoint presents the
situation as closed, and whether it focuses an interval strictly inside the situation, the source
of the preliminary-stage reading of punctuals, Section 4.2.2, are interval geometry over
`ViewpointType.ttTSitRelation`, and Table 1 is recovered as four iff theorems. -/

/-- The viewpoint asserts the initial point of the situation. -/
def ShowsInitialPoint (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.fst ∈ tt

/-- The viewpoint asserts the final point of the situation. -/
def ShowsFinalPoint (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.snd ∈ tt

/-- The viewpoint presents the situation as closed: the topic time reaches its final point. -/
def PresentsClosed (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.snd ≤ tt.snd

/-- The viewpoint focuses a topic time strictly inside the situation. -/
def FocusesPreliminaryStages (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tt < tsit

private theorem rel_imperfective :
    ViewpointType.imperfective.ttTSitRelation (⟨⟨1, 2⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 3⟩, by omega⟩ := by
  decide

private theorem rel_perfect :
    ViewpointType.perfect.ttTSitRelation (⟨⟨3, 4⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 2⟩, by omega⟩ := by
  decide

private theorem rel_prospective :
    ViewpointType.prospective.ttTSitRelation (⟨⟨0, 1⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨2, 3⟩, by omega⟩ := by
  decide

private theorem rel_neutral_short :
    ViewpointType.neutral.ttTSitRelation (⟨⟨0, 1⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 5⟩, by omega⟩ := by
  decide

private theorem rel_neutral_wide :
    ViewpointType.neutral.ttTSitRelation (⟨⟨0, 10⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 5⟩, by omega⟩ := by
  decide

private theorem rel_perfective_refl :
    ViewpointType.perfective.ttTSitRelation (⟨⟨0, 1⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 1⟩, by omega⟩ := by
  decide

/-- Table 1, the initial point: the perfective and the neutral viewpoint assert it. -/
theorem showsInitialPoint_iff (v : ViewpointType) :
    ShowsInitialPoint v ↔ v = .perfective ∨ v = .neutral := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | perfective => exact Or.inl rfl
    | neutral => exact Or.inr rfl
    | imperfective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_imperfective
        have : (1 : ℤ) ≤ 0 := hC.1
        omega
    | perfect =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfect
        have : (3 : ℤ) ≤ 0 := hC.1
        omega
    | prospective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_prospective
        have : (2 : ℤ) ≤ 1 := hC.2
        omega
  · rintro (rfl | rfl)
    · intro _ _ tt tsit h
      exact ⟨h.1, le_trans tsit.fst_le_snd h.2⟩
    · intro _ _ _ _ h
      exact h.2

/-- Table 1, the final point: only the perfective asserts it. -/
theorem showsFinalPoint_iff (v : ViewpointType) : ShowsFinalPoint v ↔ v = .perfective := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | perfective => rfl
    | imperfective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_imperfective
        have : (3 : ℤ) ≤ 2 := hC.2
        omega
    | perfect =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfect
        have : (3 : ℤ) ≤ 2 := hC.1
        omega
    | prospective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_prospective
        have : (3 : ℤ) ≤ 1 := hC.2
        omega
    | neutral =>
        exfalso
        have hC := @h ℤ _ _ _ rel_neutral_short
        have : (5 : ℤ) ≤ 1 := hC.2
        omega
  · rintro rfl
    intro _ _ tt tsit h
    exact ⟨le_trans h.1 tsit.fst_le_snd, h.2⟩

/-- Table 1, closure: the perfective and the perfect present the situation as closed. -/
theorem presentsClosed_iff (v : ViewpointType) :
    PresentsClosed v ↔ v = .perfective ∨ v = .perfect := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | perfective => exact Or.inl rfl
    | perfect => exact Or.inr rfl
    | imperfective =>
        exfalso
        have : (3 : ℤ) ≤ 2 := @h ℤ _ _ _ rel_imperfective
        omega
    | prospective =>
        exfalso
        have : (3 : ℤ) ≤ 1 := @h ℤ _ _ _ rel_prospective
        omega
    | neutral =>
        exfalso
        have : (5 : ℤ) ≤ 1 := @h ℤ _ _ _ rel_neutral_short
        omega
  · rintro (rfl | rfl)
    · intro _ _ _ _ h
      exact h.2
    · intro _ _ tt _ h
      exact le_trans h tt.fst_le_snd

/-- Table 1, preliminary stages: only the imperfective places the topic time strictly inside
the situation. -/
theorem focusesPreliminaryStages_iff (v : ViewpointType) :
    FocusesPreliminaryStages v ↔ v = .imperfective := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | imperfective => rfl
    | perfective =>
        exfalso
        exact lt_irrefl _ (@h ℤ _ _ _ rel_perfective_refl)
    | perfect =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfect
        have : (4 : ℤ) ≤ 2 := hC.1.2
        omega
    | prospective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_prospective
        have : (2 : ℤ) ≤ 0 := hC.1.1
        omega
    | neutral =>
        exfalso
        have hC := @h ℤ _ _ _ rel_neutral_wide
        have : (10 : ℤ) ≤ 5 := hC.1.2
        omega
  · rintro rfl
    intro _ _ _ _ h
    exact h

/-- The perfective makes both endpoints visible and presents the situation as closed. -/
theorem perfective_closed :
    ShowsInitialPoint .perfective ∧ ShowsFinalPoint .perfective ∧ PresentsClosed .perfective :=
  ⟨(showsInitialPoint_iff _).mpr (Or.inl rfl), (showsFinalPoint_iff _).mpr rfl,
    (presentsClosed_iff _).mpr (Or.inl rfl)⟩

/-- The imperfective makes neither endpoint visible and is open. -/
theorem imperfective_open :
    ¬ ShowsInitialPoint .imperfective ∧ ¬ ShowsFinalPoint .imperfective ∧
      ¬ PresentsClosed .imperfective := by
  rw [showsInitialPoint_iff, showsFinalPoint_iff, presentsClosed_iff]
  decide

/-- The neutral viewpoint is intermediate, Section 4.2.3: the initial point visible as under the
perfective, the final point unasserted as under the imperfective, and open. -/
theorem neutral_intermediate :
    ShowsInitialPoint .neutral ∧ ¬ ShowsFinalPoint .neutral ∧ ¬ PresentsClosed .neutral := by
  refine ⟨(showsInitialPoint_iff _).mpr (Or.inr rfl), ?_, ?_⟩
  · rw [showsFinalPoint_iff]; decide
  · rw [presentsClosed_iff]; decide

/-- Only the imperfective focuses preliminary stages, the discriminator between the neutral
viewpoint and the imperfective, Section 4.2.3, (41). -/
theorem neutral_no_preliminary_stages :
    ¬ FocusesPreliminaryStages .neutral ∧ FocusesPreliminaryStages .imperfective := by
  refine ⟨?_, (focusesPreliminaryStages_iff _).mpr rfl⟩
  rw [focusesPreliminaryStages_iff]; decide

/-- The neutral viewpoint sides with the perfective on the initial point and with the
imperfective on the final point. -/
theorem neutral_between_perf_imperf :
    (ShowsInitialPoint .neutral ↔ ShowsInitialPoint .perfective) ∧
      (ShowsFinalPoint .neutral ↔ ShowsFinalPoint .imperfective) :=
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

/-- WALS Ch 65 (perfective/imperfective aspect) records grammatical aspect for
    French and Mandarin, consistent with Smith giving each both `.perfective`
    and `.imperfective` viewpoints.

    English diverges: WALS Ch 65 codes English as having no grammatical
    perfective/imperfective marking, whereas Smith analyses English as having a
    perfective/imperfective (progressive) opposition. The theorem states the
    WALS rows as they stand rather than forcing agreement with Smith's account. -/
theorem wals_aspect_rows :
    (Data.WALS.F65A.lookupISO "fra").map (·.value) = some .grammaticalMarking ∧
    (Data.WALS.F65A.lookupISO "cmn").map (·.value) = some .grammaticalMarking ∧
    (Data.WALS.F65A.lookupISO "eng").map (·.value) = some .noGrammaticalMarking := by
  decide

/-- French has the neutral viewpoint (the Futur), and WALS Ch 67 records French
    as having an inflectional future — consistent across the two encodings. -/
theorem french_neutral_has_inflectional_future :
    ViewpointType.neutral ∈ french.viewpoints ∧
    (Data.WALS.F67A.lookupISO "fra").map (·.value) = some .inflectionalFutureExists := by
  decide

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

/-- A situation type has internal stages when it is dynamic and durative, Chapter 4. -/
def HasInternalStages (c : VendlerClass) : Prop :=
  c.dynamicity = .dynamic ∧ c.duration = .durative

instance (c : VendlerClass) : Decidable (HasInternalStages c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The progressive accepts exactly the dynamic-durative classes, those with internal stages,
Chapter 4. -/
theorem progressive_requires_HasInternalStages (c : VendlerClass) :
    Aspect.progressivePrediction c = .accept ↔ HasInternalStages c := by
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
    Aspect.forXPrediction .semelfactive = .coerced :=
  ⟨rfl, rfl, rfl⟩

end Smith1997
