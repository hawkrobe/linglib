import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Theories.Semantics.Tense.Aspect.Core
import Linglib.Theories.Semantics.Tense.Aspect.Composition
import Linglib.Phenomena.TenseAspect.Studies.Rothstein2004
import Linglib.Phenomena.TenseAspect.Typology

/-!
# The Parameter of Aspect (2nd ed.)
@cite{smith-1997}

Formalizes Smith's two-component theory of aspect:
aspectual meaning = situation type × viewpoint aspect, independently combined.

## What this file exercises

- **Temporal schemata** per situation type (Ch. 2)
- **Viewpoint visibility properties** (§4.1): what each viewpoint makes visible
- **Neutral viewpoint** (§4.2.3): default for LVM sentences
- **Independence theorem** (§4.3): situation type × viewpoint freely combine
- **Cross-linguistic viewpoint parameters** (§4.2): language-specific inventories
- **Compositional rules bridge** (§3.3): connects to `Composition.lean`

## What lives elsewhere

- Situation type classification (VendlerClass): `LexicalAspect.lean`
- Viewpoint operators (IMPF, PRFV, INIT_OVERLAP): `Core.lean`
- VP-level composition rules: `Composition.lean`
- Aspectual diagnostics: `Rothstein2004.lean`

-/

open Phenomena.TenseAspect

namespace Smith1997

open Core (WorldTimeIndex)

open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open Semantics.Tense.Aspect.Core (ViewpointType)
open Semantics.Tense.Aspect.Composition
open Phenomena.TenseAspect.Diagnostics (DiagnosticResult)

-- ════════════════════════════════════════════════════
-- § 1. Temporal Schemata
-- ════════════════════════════════════════════════════

/-! Smith Ch. 2: each situation type has a characteristic temporal schema
    defining its internal temporal structure.

    - States: (I)——(F)          unbounded, no internal stages
    - Activities: I......F_Arb  arbitrary final point, internal stages
    - Accomplishments: I.....F_Nat R  natural final point + result
    - Semelfactives: E          single instantaneous stage
    - Achievements: ...E_R...   instantaneous + result state

    We encode the structural properties of each schema. -/

/-- Whether the situation type has a natural (non-arbitrary) final point.
    Telic types have natural endpoints; atelic types don't.
    This is exactly the telicity feature, named for Smith's terminology.

    Note: `hasNaturalEndpoint` coincides extensionally with `hasResultState`
    in our 3-feature system (both reduce to telicity), but the concepts
    differ in Smith's presentation: a natural endpoint is a property of the
    temporal schema's boundary structure, while a result state is the
    post-final-point stage (the built house, the won race). We retain
    `hasNaturalEndpoint` as the primary predicate and derive result-state
    presence from it via `resultState_iff_naturalEndpoint`. -/
def hasNaturalEndpoint (c : VendlerClass) : Bool := c.telicity == .telic

/-- Whether the situation type has internal stages (intervals of change).
    Dynamic + durative types have internal stages; states and punctuals don't.
    Smith Ch. 4: the progressive focuses internal stages, so types without
    them resist the progressive. -/
def hasInternalStages (c : VendlerClass) : Bool :=
  c.dynamicity == .dynamic && c.duration == .durative

/-- Whether the situation type has detachable preliminary stages that
    the imperfective can focus independently of the event itself.

    Smith §4.2.2 (p. 75): achievements have preliminary stages —
    processes leading to the instantaneous change ("The team was reaching
    the top" presents preliminary stages, not the reaching itself).
    Semelfactives, also instantaneous, do NOT have preliminary stages
    and never appear with imperfectives focusing a preliminary interval.

    Accomplishments also have process stages, but these are *non-detachable*:
    the process IS the event (building a house). The imperfective focuses
    internal stages of the event proper, not separate preliminary stages.
    This detachability distinction is why `hasPreliminaryStages` is true
    only for achievements. -/
def hasPreliminaryStages (c : VendlerClass) : Bool :=
  c == .achievement

-- Schema verification

/-- Activities have internal stages but no natural endpoint. -/
theorem activity_schema :
    hasInternalStages .activity = true ∧
    hasNaturalEndpoint .activity = false := ⟨rfl, rfl⟩

/-- Accomplishments have internal stages AND a natural endpoint. -/
theorem accomplishment_schema :
    hasInternalStages .accomplishment = true ∧
    hasNaturalEndpoint .accomplishment = true := ⟨rfl, rfl⟩

/-- Semelfactives: single stage, no internal structure, no endpoint,
    no preliminary stages. Contrasts with achievements on all three
    schema properties despite sharing [−durative]. -/
theorem semelfactive_schema :
    hasInternalStages .semelfactive = false ∧
    hasNaturalEndpoint .semelfactive = false ∧
    hasPreliminaryStages .semelfactive = false := ⟨rfl, rfl, rfl⟩

/-- Achievements: instantaneous with natural endpoint, and detachable
    preliminary stages that the imperfective can focus. -/
theorem achievement_schema :
    hasInternalStages .achievement = false ∧
    hasNaturalEndpoint .achievement = true ∧
    hasPreliminaryStages .achievement = true := ⟨rfl, rfl, rfl⟩

/-- States: no internal stages, no natural endpoint. -/
theorem state_schema :
    hasInternalStages .state = false ∧
    hasNaturalEndpoint .state = false := ⟨rfl, rfl⟩

/-- Result states coincide with natural endpoints in the 3-feature system.
    Both reduce to telicity. Conceptually distinct in Smith's presentation
    (endpoint = schema boundary, result = post-final stage), but our
    feature decomposition doesn't distinguish them — both are consequences
    of [+telic]. -/
theorem resultState_iff_naturalEndpoint (c : VendlerClass) :
    hasNaturalEndpoint c = (c.telicity == .telic) := rfl

-- ════════════════════════════════════════════════════
-- § 2. Viewpoint Visibility
-- ════════════════════════════════════════════════════

/-! Smith §4.1: viewpoints differ in what they make visible.

    | Viewpoint     | Initial pt | Internal stages | Final pt |
    |---------------|------------|----------------|----------|
    | Perfective    | visible    | visible        | visible  |
    | Imperfective  | not vis.   | visible        | not vis. |
    | Neutral       | visible    | ≥1 stage       | open     |

    The neutral viewpoint is informationally between perfective
    and imperfective: it always includes I (like perfective) but
    F may or may not be visible (unlike either). -/

/-- Whether the viewpoint makes the initial point visible. -/
def showsInitialPoint : ViewpointType → Bool
  | .perfective => true
  | .imperfective => false
  | .neutral => true
  | .perfect => false      -- perfect focuses the post-state, not the event's I
  | .prospective => false  -- prospective focuses pre-state

/-- Whether the viewpoint makes the final point visible (asserted). -/
def showsFinalPoint : ViewpointType → Bool
  | .perfective => true
  | .imperfective => false
  | .neutral => false    -- F may be inferred but is not asserted
  | .perfect => false
  | .prospective => false

/-- Whether the viewpoint presents a closed (completed) situation. -/
def isClosed : ViewpointType → Prop
  | .perfective => True
  | .imperfective => False
  | .neutral => False    -- neutral allows both open AND closed readings
  | .perfect => True     -- perfect presents completed event within PTS
  | .prospective => False

instance : DecidablePred isClosed := fun x => by cases x <;> unfold isClosed <;> infer_instance

/-- Perfective is informationally closed: both I and F visible. -/
theorem perfective_closed :
    showsInitialPoint .perfective = true ∧
    showsFinalPoint .perfective = true ∧
    isClosed .perfective := ⟨rfl, rfl, trivial⟩

/-- Imperfective is informationally open: neither I nor F visible. -/
theorem imperfective_open :
    showsInitialPoint .imperfective = false ∧
    showsFinalPoint .imperfective = false ∧
    ¬ isClosed .imperfective := ⟨rfl, rfl, not_false⟩

/-- Neutral includes I but not necessarily F — intermediate informativity. -/
theorem neutral_intermediate :
    showsInitialPoint .neutral = true ∧
    showsFinalPoint .neutral = false ∧
    ¬ isClosed .neutral := ⟨rfl, rfl, not_false⟩

/-- Whether the viewpoint can focus preliminary stages of an event.
    @cite{smith-1997} §4.2.2 (p. 75): imperfective viewpoints may focus
    preliminary stages of achievements ("The team was reaching the top").
    §4.2.3 (p. 80): neutral viewpoints do NOT focus preliminary stages —
    this is a key discriminator between neutral and imperfective.

    French Futur achievements cannot conjoin with assertions that the
    event didn't occur (p. 80, ex. 41): # "La guerre éclaira mais elle
    n'éclaira pas." Unlike imperfectives, which can present preliminary
    stages without entailing the event occurs.

    Perfective viewpoints don't focus preliminary stages either — they
    present the event as a whole (or closed). -/
def focusesPreliminaryStages : ViewpointType → Bool
  | .imperfective => true   -- "The team was reaching the top" (preliminary)
  | .perfective => false    -- presents the whole event
  | .neutral => false       -- does NOT allow preliminary readings
  | .perfect => false       -- focuses post-state
  | .prospective => false   -- focuses pre-state

/-- Neutral viewpoints do not focus preliminary stages, unlike
    imperfectives. This is the key discrimination: "La guerre éclaira"
    (neutral/Futur) does NOT have the preliminary reading available
    to "La guerre était en train d'éclater" (imperfective). -/
theorem neutral_no_preliminary_stages :
    focusesPreliminaryStages .neutral = false ∧
    focusesPreliminaryStages .imperfective = true := ⟨rfl, rfl⟩

/-- The neutral viewpoint is strictly between perfective and imperfective
    in informativity: it shows I (like perfective, unlike imperfective)
    but doesn't assert F (like imperfective, unlike perfective). -/
theorem neutral_between_perf_imperf :
    showsInitialPoint .neutral = showsInitialPoint .perfective ∧
    showsFinalPoint .neutral = showsFinalPoint .imperfective := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Independence of Situation Type and Viewpoint
-- ════════════════════════════════════════════════════

/-! Smith §4.3: the two components of aspectual meaning are independent.
    Any situation type can combine with any viewpoint. The 5 × 4 product
    is freely generated — there are no gaps.

    This is the core structural claim of the two-component theory. We
    verify it by showing that `ViewpointType` and `VendlerClass` are
    independently enumerable and that each combination is distinct. -/

/-- An aspectual interpretation: the combination of situation type and
    viewpoint. This is the "two-component" structure. -/
structure AspectualInterpretation where
  situationType : VendlerClass
  viewpoint : ViewpointType
  deriving DecidableEq, Repr

/-- All 20 combinations of situation type × viewpoint. -/
def allSitTypes : List VendlerClass :=
  [.state, .activity, .achievement, .accomplishment, .semelfactive]

def allViewpoints : List ViewpointType :=
  [.perfective, .imperfective, .neutral, .perfect, .prospective]

def allInterpretations : List AspectualInterpretation :=
  allSitTypes.flatMap (λ st => allViewpoints.map (λ vp => ⟨st, vp⟩))

/-- The product is freely generated: 25 distinct combinations. -/
theorem independence_free_generation :
    allInterpretations.length = 25 := by native_decide

/-- No duplicates in the product — all combinations are distinct. -/
theorem independence_no_duplicates :
    allInterpretations.Nodup := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Cross-Linguistic Viewpoint Parameters
-- ════════════════════════════════════════════════════

/-! Smith §4.2: languages differ in their viewpoint inventories.
    Three parameters:
    1. Which viewpoints are available
    2. Which is the default (dominant) viewpoint
    3. Whether/how statives participate in the perfective system

    These parameters are the "parameter of aspect" — the locus of
    cross-linguistic variation within the universal two-component theory. -/

/-- How the perfective viewpoint interacts with statives.
    @cite{smith-1997} pp. 69-70 identifies three cross-linguistic patterns:

    - **closed**: perfective covers statives with a closed interpretation
      (French: "Marie a vécu à Paris" — asserts the situation is over)
    - **open**: perfective appears with stative verb constellations but
      allows both open and closed readings (English: "Jennifer knew Turkish"
      — she may or may not still know it)
    - **excluded**: perfective does not apply to statives at all
      (Russian, Chinese, Navajo — no perfective stative sentences) -/
inductive PerfStativeParam where
  | closed    -- perfective covers statives, asserts closure (French)
  | open      -- perfective with statives, open or closed (English)
  | excluded  -- perfective does not apply to statives (Russian, Chinese, Navajo)
  deriving DecidableEq, Repr

/-- A language's aspectual system parameters. -/
structure AspectualSystem where
  /-- Language name -/
  language : String
  /-- Available viewpoint types -/
  viewpoints : List ViewpointType
  /-- Default viewpoint for aspectually vague sentences -/
  defaultViewpoint : ViewpointType
  /-- How the perfective interacts with statives -/
  perfStativeParam : PerfStativeParam
  deriving Repr

/-- English: perfective + imperfective (progressive); no neutral;
    perfective with statives allows open or closed readings
    (@cite{smith-1997} p. 70: "Jennifer knew Turkish" — she may still
    know it or may have forgotten). -/
def english : AspectualSystem :=
  { language := "English"
  , viewpoints := [.perfective, .imperfective]
  , defaultViewpoint := .perfective
  , perfStativeParam := .open }

/-- French: perfective + imperfective + neutral (Futur);
    perfective covers statives with closed reading
    (@cite{smith-1997} p. 70: "Marie a vécu à Paris" — asserts
    the situation is over; # "Marie a vécu à Paris et elle y vit encore"). -/
def french : AspectualSystem :=
  { language := "French"
  , viewpoints := [.perfective, .imperfective, .neutral]
  , defaultViewpoint := .perfective
  , perfStativeParam := .closed }

/-- Mandarin: perfective (-le) + imperfective (zai, -zhe) + neutral (bare);
    perfective does NOT apply to statives. -/
def mandarin : AspectualSystem :=
  { language := "Mandarin"
  , viewpoints := [.perfective, .imperfective, .neutral]
  , defaultViewpoint := .neutral
  , perfStativeParam := .excluded }

/-- Navajo: perfective + imperfective + neutral (Usitative/Iterative);
    perfective does NOT apply to statives. -/
def navajo : AspectualSystem :=
  { language := "Navajo"
  , viewpoints := [.perfective, .imperfective, .neutral]
  , defaultViewpoint := .neutral
  , perfStativeParam := .excluded }

/-- All four languages have at least perfective and imperfective. -/
theorem universal_core :
    [english, french, mandarin, navajo].all
      (λ sys => sys.viewpoints.contains .perfective &&
                sys.viewpoints.contains .imperfective) = true := by
  native_decide

/-- The neutral viewpoint appears in languages with LVM sentences. -/
theorem neutral_in_lvm_languages :
    french.viewpoints.contains .neutral = true ∧
    mandarin.viewpoints.contains .neutral = true ∧
    navajo.viewpoints.contains .neutral = true := ⟨rfl, rfl, rfl⟩

/-- English lacks the neutral viewpoint. -/
theorem english_no_neutral :
    english.viewpoints.contains .neutral = false := rfl

/-- The three perfective-stative patterns are all distinct. -/
theorem three_perf_stative_patterns :
    english.perfStativeParam = .open ∧
    french.perfStativeParam = .closed ∧
    mandarin.perfStativeParam = .excluded ∧
    navajo.perfStativeParam = .excluded := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4b. WALS Typology Bridge
-- ════════════════════════════════════════════════════

/-! Smith's viewpoint inventories and the WALS typological profiles
    (`Typology.lean`) describe the same languages at different levels:
    Smith identifies *which* viewpoints a language has; WALS records
    *whether* the perfective/imperfective distinction is grammaticalized.

    All four Smith languages grammaticalize this distinction (WALS Ch 65
    = `.grammatical`), which is consistent with their viewpoint inventories
    containing both `.perfective` and `.imperfective`. -/

open Phenomena.TenseAspect.Typology in

/-- Languages in Smith's sample all have grammaticalized aspect in WALS.
    This is expected: Smith's viewpoint inventory presupposes the
    perfective/imperfective contrast is grammatically expressed. -/
theorem smith_languages_have_wals_aspect :
    Typology.english.aspect = .grammatical ∧
    Typology.french.aspect = .grammatical ∧
    Typology.mandarin.aspect = .grammatical := ⟨rfl, rfl, rfl⟩

/-- Smith's French has the neutral viewpoint (Futur);
    WALS French has inflectional future — consistent, since the
    Futur is the morphological expression of the neutral viewpoint. -/
theorem french_neutral_has_inflectional_future :
    french.viewpoints.contains .neutral = true ∧
    Typology.french.future = .inflectional := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Viewpoint × Situation Type Interactions
-- ════════════════════════════════════════════════════

/-! Smith Ch. 4: although the components are independent, their
    interaction produces predictable interpretive effects. -/

/-- The imperfective paradox arises exactly when the viewpoint is
    imperfective and the situation type is telic.
    "Mary was walking to school" does not entail "Mary walked to school".
    The paradox doesn't arise for atelic types (activities, states)
    because their subinterval property makes IMPF entail PRFV. -/
def imperfectiveParadoxArises (ai : AspectualInterpretation) : Bool :=
  ai.viewpoint == .imperfective && ai.situationType.telicity == .telic

/-- The paradox arises for imperfective accomplishments. -/
theorem paradox_impf_accomplishment :
    imperfectiveParadoxArises ⟨.accomplishment, .imperfective⟩ = true := rfl

/-- The paradox does not arise for imperfective activities. -/
theorem no_paradox_impf_activity :
    imperfectiveParadoxArises ⟨.activity, .imperfective⟩ = false := rfl

/-- The paradox never arises with perfective viewpoint. -/
theorem no_paradox_perfective (c : VendlerClass) :
    imperfectiveParadoxArises ⟨c, .perfective⟩ = false := rfl

/-- Whether the perfective conveys *completion* (reaching the natural
    endpoint) or merely *termination* (stopping).
    @cite{smith-1997} pp. 67-68: "The Activity sentence conveys
    termination (Lily stopped swimming) whereas the Accomplishment
    conveys completion (Mrs Ramsey finished the letter)."

    - Perfective + telic → completion (the endpoint was reached)
    - Perfective + atelic → termination (the event stopped)
    - Non-perfective viewpoints don't assert either -/
inductive PerfectiveEffect where
  | completion    -- natural endpoint reached (telic)
  | termination   -- event stopped without reaching an endpoint (atelic)
  | noEffect      -- not perfective, no completion/termination asserted
  deriving DecidableEq, Repr

/-- Determine the perfective effect from an aspectual interpretation. -/
def perfectiveEffect (ai : AspectualInterpretation) : PerfectiveEffect :=
  match ai.viewpoint with
  | .perfective =>
    if ai.situationType.telicity == .telic then .completion else .termination
  | _ => .noEffect

/-- Perfective accomplishments convey completion.
    "Mrs Ramsey wrote a letter" → she finished it (# "she didn't finish it"). -/
theorem perf_accomplishment_completes :
    perfectiveEffect ⟨.accomplishment, .perfective⟩ = .completion := rfl

/-- Perfective activities convey termination, not completion.
    "Lily swam in the pond" → she stopped swimming (not *completed* swimming). -/
theorem perf_activity_terminates :
    perfectiveEffect ⟨.activity, .perfective⟩ = .termination := rfl

/-- Perfective achievements convey completion (instantaneous endpoint). -/
theorem perf_achievement_completes :
    perfectiveEffect ⟨.achievement, .perfective⟩ = .completion := rfl

/-- Imperfective viewpoints don't assert completion or termination. -/
theorem impf_no_completion_termination (c : VendlerClass) :
    perfectiveEffect ⟨c, .imperfective⟩ = .noEffect := rfl

/-- Completion vs termination tracks telicity exactly: telic situations
    complete, atelic situations merely terminate. -/
theorem completion_iff_telic (c : VendlerClass) :
    perfectiveEffect ⟨c, .perfective⟩ = .completion ↔
    c.telicity = .telic := by
  cases c <;> simp [perfectiveEffect, VendlerClass.telicity]

/-- Progressive requires internal stages (durative + dynamic).
    This is derived from the feature decomposition, not stipulated
    per class — connecting to `progressive_from_features` in
    Rothstein2004.lean. -/
theorem progressive_requires_stages (c : VendlerClass) :
    Diagnostics.progressivePrediction c = .accept ↔
    hasInternalStages c = true := by
  cases c <;> simp [Diagnostics.progressivePrediction, hasInternalStages,
    VendlerClass.dynamicity, VendlerClass.duration]

-- ════════════════════════════════════════════════════
-- § 6. Compositional Rule Verification
-- ════════════════════════════════════════════════════

/-! Connect Smith's compositional rules (§3.3) to `Composition.lean`
    and verify against Smith's examples. -/

/-- Smith's external override (§3.2.5) is idempotent and absorbs
    prior composition — the override is the final word. -/
theorem external_override_is_final (v : AspectualProfile) (np : MassCount)
    (ext : Telicity) :
    (overrideTelicity (composeWithNP v np) ext).telicity = ext := rfl

/-- The count/mass distinction in NPs tracks cumulativity/quantization:
    count NPs are quantized (QUA), mass NPs are cumulative (CUM).
    This connects Smith's compositional rules to Krifka's mereological
    telicity theory via the bridge in `Events/Mereology.lean`.

    - V[+Telic] + NP[+Count/QUA] → VCon[+Telic] (telic preserved)
    - V[+Telic] + NP[-Count/CUM] → VCon[-Telic] (atelicized)

    These are the same predictions as `eat_two_apples_telic` and
    `eat_apples_atelic` in `Krifka1998.lean`. -/
theorem krifka_smith_agreement :
    (composeWithNP accomplishmentProfile .count).telicity = .telic ∧
    (composeWithNP accomplishmentProfile .mass).telicity = .atelic := ⟨rfl, rfl⟩

/-- Semelfactive coercion under duration is compositionally derived:
    VCon[+Dyn, -Tel, -Dur] + [+Dur] → DVCon[+Dyn, -Tel, +Dur] = Activity.
    This matches `duratize_semelfactive` in LexicalAspect.lean and
    `semelfactive_durative_is_activity` in Composition.lean. -/
theorem semelfactive_coercion_three_ways :
    semelfactiveProfile.duratize.toVendlerClass = .activity ∧
    (overrideDuration semelfactiveProfile .durative).toVendlerClass = .activity ∧
    Diagnostics.forXPrediction .semelfactive = .coerced := ⟨rfl, rfl, rfl⟩

end Smith1997
