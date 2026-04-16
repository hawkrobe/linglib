import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Theories.Semantics.Lexical.Adjective.Intensification
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Scales.Scale

/-!
# Beltrama 2025: Evaluation, thresholds, and practical commitments

@cite{beltrama-2025}

Beltrama, A. (2025). Evaluation, thresholds, and practical commitments:
the grammar of adjectival mildness. *Natural Language Semantics* 33, 169--205.

## Core claims

1. **MPAs** (*decent*, *acceptable*, *adequate*) are a novel class of gradable
   predicates with a hybrid profile overlapping both relative and absolute adjectives.

2. MPAs encode a **necessity standard**: the minimum value required for an object's
   pursuit to be possible given the norms and circumstances in the current world.
   This is a *functional standard* (cf. @cite{kagan-alexeyenko-2011}), not a
   distributional (contextual) or endpoint standard.

3. The **middling inference** ("not great") is a scalar implicature, not hardwired
   semantics: it is cancelable, reinforceable, and suspended in DE contexts.

4. The **standard function s** must be generalized beyond @cite{kennedy-2007}'s
   Principle of Interpretive Economy to handle functional standards.

## Key formal definitions

- `⟦MPA⟧ = λx. μ_value(x)` — basic entry (measure function returning value)
- `s(MPA) = Max({d : ∀w' ∈ Acc(w)[PURSUED(x)(w') → μ_value(x)(w') ≥ d]})`
  — necessity standard (functional)
- `⟦POS MPA⟧ = λx. μ_value(x)(w) ≥ s(MPA)` — positive form
-/

namespace Beltrama2025

open Core.Scale (Boundedness)
open Semantics.Degree (PositiveStandard interpretiveEconomy positiveMeaning)
open Semantics.Degree (AdjectiveClass)

-- ============================================================================
-- § 1. Empirical Profile (Table 1)
-- ============================================================================

/-- Properties distinguishing MPAs from *good* (Table 1, p. 179).

Each field is `true` when the property holds for the adjective class. -/
structure EmpiricalProfile where
  contextSensitive   : Bool  -- sensitive to comparison class / purpose
  gradable           : Bool  -- combinable with degree morphology
  zoneOfIndifference : Bool  -- neither P nor antonym(P) yields contradiction
  borderlineCases    : Bool  -- can fall in a borderline region
  combinesBarely     : Bool  -- felicitous with *barely*
  emphasisInDE       : Bool  -- produces emphasis under negation / *even*
  ableDerivation     : Bool  -- systematically derived via *-able*
  deriving Repr, DecidableEq

/-- MPAs: context-sensitive, gradable, no zone of indifference,
    no borderline cases, combines with *barely*, emphatic in DE contexts,
    productively derived via *-able*. -/
def mpaProfile : EmpiricalProfile :=
  { contextSensitive   := true
  , gradable           := true   -- but restricted: resists *very*, *extremely*
  , zoneOfIndifference := false
  , borderlineCases    := false
  , combinesBarely     := true
  , emphasisInDE       := true
  , ableDerivation     := true }

/-- *good*: context-sensitive, gradable, zone of indifference present,
    borderline cases present, resists *barely* (unless special context),
    mostly no emphasis in DE, no *-able* derivation. -/
def goodProfile : EmpiricalProfile :=
  { contextSensitive   := true
  , gradable           := true
  , zoneOfIndifference := true
  , borderlineCases    := true
  , combinesBarely     := false
  , emphasisInDE       := false
  , ableDerivation     := false }

/-- MPAs and *good* agree on context-sensitivity and gradability. -/
theorem mpa_good_share_context_gradability :
    mpaProfile.contextSensitive = goodProfile.contextSensitive ∧
    mpaProfile.gradable = goodProfile.gradable := ⟨rfl, rfl⟩

/-- MPAs and *good* diverge on zone of indifference, borderline cases,
    *barely* compatibility, and emphasis. -/
theorem mpa_good_diverge :
    mpaProfile.zoneOfIndifference ≠ goodProfile.zoneOfIndifference ∧
    mpaProfile.borderlineCases ≠ goodProfile.borderlineCases ∧
    mpaProfile.combinesBarely ≠ goodProfile.combinesBarely ∧
    mpaProfile.emphasisInDE ≠ goodProfile.emphasisInDE := by
  exact ⟨by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- § 2. Scale Structure
-- ============================================================================

/-- The value scale is lower-bounded at 0 (purpose-thwarting → purpose-serving),
    open above. Following @cite{wolfsdorf-2019} and @cite{qing-2021}. -/
def valueScaleBoundedness : Boundedness := .lowerBounded

/-- Interpretive Economy would predict a minEndpoint standard for a
    lower-bounded scale — but this is wrong for both *good* (which gets
    a contextual standard) and MPAs (which get a functional standard).
    This shows IE must be generalized for evaluative predicates. -/
theorem ie_underpredicts_for_value_scale :
    interpretiveEconomy valueScaleBoundedness = .minEndpoint := rfl

-- ============================================================================
-- § 3. Standard Types: MPA vs Good vs MinSAA
-- ============================================================================

/-- *good* receives a contextual standard despite being on a lower-bounded
    scale — an exception to Interpretive Economy. The standard is determined
    by the distribution of objects in the comparison class, as with other
    relative (Class A) adjectives like *tall*. -/
def goodStandard : PositiveStandard := .contextual

/-- MPAs receive a functional (necessity) standard — the minimum value
    required for the object's pursuit to be circumstantially possible. -/
def mpaStandard : PositiveStandard := .functional

/-- MinSAAs (*wet*, *profitable*) receive a minEndpoint standard — any
    nonzero degree suffices. -/
def minsaaStandard : PositiveStandard := .minEndpoint

/-- All three standard types for evaluative predicates on the value scale
    are distinct. -/
theorem three_standards_distinct :
    goodStandard ≠ mpaStandard ∧
    mpaStandard ≠ minsaaStandard ∧
    goodStandard ≠ minsaaStandard := by
  exact ⟨by decide, by decide, by decide⟩

/-- MPAs and *good* both require comparison classes (context-sensitive),
    unlike MinSAAs. -/
theorem mpa_good_both_cc_sensitive :
    mpaStandard.requiresComparisonClass = true ∧
    goodStandard.requiresComparisonClass = true ∧
    minsaaStandard.requiresComparisonClass = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 4. MinSAA Rejection (@cite{beltrama-2025} §4)
-- ============================================================================

/-- The MinSAA hypothesis: MPAs are minimum-standard absolute adjectives.
    This is initially plausible — lower-bounded scale, s(MPA) = 0 — but
    §4.2 shows it makes incorrect predictions. -/
structure MinSAAHypothesis where
  /-- *slightly* compatible (MinSAAs: yes; MPAs: no) -/
  slightlyOk      : Bool
  /-- Context-sensitive (MinSAAs: no; MPAs: yes) -/
  contextSensitive : Bool
  /-- Comparative entails positive form (MinSAAs: yes; MPAs: no) -/
  compEntailsPos   : Bool
  /-- Denial cancels all degree (MinSAAs: yes; MPAs: no) -/
  denialCancels    : Bool
  deriving Repr, DecidableEq

/-- MinSAA predictions: *slightly* OK, not CC-sensitive, comparative
    entails positive form, denial cancels all degree. -/
def minsaaPredictions : MinSAAHypothesis :=
  { slightlyOk := true, contextSensitive := false
  , compEntailsPos := true, denialCancels := true }

/-- MPA actual behavior: *slightly* blocked, CC-sensitive, comparative
    does NOT entail positive form, denial does NOT cancel all degree. -/
def mpaActual : MinSAAHypothesis :=
  { slightlyOk := false, contextSensitive := true
  , compEntailsPos := false, denialCancels := false }

/-- MinSAA predictions diverge from MPA behavior on ALL four diagnostics.
    This is the core argument of §4.2 for rejecting the MinSAA analysis. -/
theorem minsaa_hypothesis_rejected :
    minsaaPredictions ≠ mpaActual := by decide

-- ============================================================================
-- § 5. Necessity Standard (Formal Definition)
-- ============================================================================

/-- A simplified finite model for the necessity standard.

    The accessibility relation is exclusively **circumstantial**
    (@cite{beltrama-2025} p. 196): the accessible worlds are those
    compatible with the norms and circumstances in the current world.

- `W` — possible worlds
- `μ` — measure function (value of the object in each world)
- `acc` — circumstantially accessible worlds from the evaluation world
- `pursued` — whether the object is pursued in a given world
-/
structure NecStandardModel (W : Type) where
  μ       : W → Nat          -- μ_value: value of the object
  acc     : List W            -- Circ(w): circumstantially accessible worlds
  pursued : W → Bool          -- PURSUED(x): object is pursued

/-- The necessity standard: the maximum degree *d* such that in ALL
    circumstantially accessible worlds where the object is pursued,
    its value is at least *d*.

    s(MPA) = Max({d : ∀w' ∈ Circ(w)[PURSUED(x)(w') → μ(x)(w') ≥ d]})

    This returns the minimum value of μ across pursued accessible worlds.
    If nothing is pursued, the universal is vacuously true for all *d*,
    so the standard is maximally high (we return `max` of μ over all
    accessible worlds, defaulting to 0 if `acc` is empty). -/
def necessityStandard {W : Type} (m : NecStandardModel W) : Nat :=
  let pursuedWorlds := m.acc.filter m.pursued
  match pursuedWorlds with
  | []     => -- Vacuous case: standard is maximally high
    match m.acc with
    | []     => 0
    | w :: ws => ws.foldl (fun a w' => max a (m.μ w')) (m.μ w)
  | w :: ws => ws.foldl (fun a w' => min a (m.μ w')) (m.μ w)

/-- The positive form: μ_value(x)(w) ≥ s(MPA). -/
def mpaPositiveForm {W : Type} (m : NecStandardModel W) (actualValue : Nat) : Bool :=
  actualValue ≥ necessityStandard m

-- ============================================================================
-- § 5. Degree Modifier Compatibility
-- ============================================================================

/-- Degree modifier compatibility data for MPAs.

@cite{beltrama-2025} §2.2.2, §6.4--6.5:
- *quite/pretty/somewhat*: OK (moderate degree)
- *very/extremely/super*: degraded (conflict with middling flavor)
- *barely*: OK (necessity standard provides crisp boundary)
- *slightly*: blocked (value scale minimum is 0, but MPA standard ≠ 0) -/
structure ModifierCompatibility where
  form          : String
  quite         : Bool  -- moderate intensifiers
  veryExtremely : Bool  -- strong intensifiers
  barely        : Bool  -- proximal modifier
  slightly      : Bool  -- minimal degree
  deriving Repr

def decentModifiers : ModifierCompatibility :=
  { form := "decent", quite := true, veryExtremely := false
  , barely := true, slightly := false }

def goodModifiers : ModifierCompatibility :=
  { form := "good", quite := true, veryExtremely := true
  , barely := false, slightly := false }

/-- MPAs combine with *barely* while *good* doesn't. -/
theorem mpa_barely_vs_good :
    decentModifiers.barely = true ∧ goodModifiers.barely = false := ⟨rfl, rfl⟩

/-- Both MPAs and *good* resist *slightly*. -/
theorem both_resist_slightly :
    decentModifiers.slightly = false ∧ goodModifiers.slightly = false := ⟨rfl, rfl⟩

/-- MPAs resist strong intensifiers while *good* accepts them. -/
theorem mpa_resists_strong_intensifiers :
    decentModifiers.veryExtremely = false ∧
    goodModifiers.veryExtremely = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6. Fragment Entry Verification
-- ============================================================================

open Fragments.English.Predicates.Adjectival (decent acceptable adequate good)

/-- All MPA fragment entries use the value dimension. -/
theorem mpa_entries_value_dimension :
    decent.dimension = .value ∧
    acceptable.dimension = .value ∧
    adequate.dimension = .value := ⟨rfl, rfl, rfl⟩

/-- All MPA fragment entries have lower-bounded scales. -/
theorem mpa_entries_lower_bounded :
    decent.scaleType = .lowerBounded ∧
    acceptable.scaleType = .lowerBounded ∧
    adequate.scaleType = .lowerBounded := ⟨rfl, rfl, rfl⟩

/-- *good* shares the same scale structure as MPAs. -/
theorem good_same_scale_as_mpas :
    good.scaleType = decent.scaleType ∧
    good.dimension = decent.dimension := ⟨rfl, rfl⟩

/-- Despite sharing scale structure, *good* and MPAs receive different
    standards. IE predicts minEndpoint for both, but *good* overrides to
    contextual and MPAs override to functional. This division of labor
    is what makes the system maximally informative. -/
theorem good_vs_mpa_standard_override :
    goodStandard ≠ mpaStandard := by decide

-- ============================================================================
-- § 7. Middling Inference as Scalar Implicature
-- ============================================================================

/-- The middling inference is a scalar implicature, not lexical semantics.
    Evidence: cancelability, reinforceability, suspension in DE contexts.

    Scale: ⟨decent, good, great, fantastic⟩
    Using *decent* implicates ¬*good* (speaker would have used *good* if true).
    This is the standard Horn/Grice reasoning over evaluative scales. -/
inductive EvaluativeAlternative where
  | decent | good | great | fantastic
  deriving DecidableEq, Repr

/-- Evaluative scale ordering: decent < good < great < fantastic. -/
def EvaluativeAlternative.rank : EvaluativeAlternative → Nat
  | .decent    => 0
  | .good      => 1
  | .great     => 2
  | .fantastic => 3

/-- The middling inference: using a weaker alternative implicates the
    negation of all stronger alternatives. -/
def middlingInference (uttered : EvaluativeAlternative)
    (alt : EvaluativeAlternative) : Bool :=
  alt.rank > uttered.rank

/-- Using *decent* generates implicatures against *good*, *great*, *fantastic*. -/
theorem decent_implicates_not_good :
    middlingInference .decent .good = true ∧
    middlingInference .decent .great = true ∧
    middlingInference .decent .fantastic = true := ⟨rfl, rfl, rfl⟩

/-- Using *good* does NOT generate the middling inference (no stronger
    alternative is conventionally excluded). -/
theorem good_no_middling_against_decent :
    middlingInference .good .decent = false := rfl

-- ============================================================================
-- § 8. Non-Vague Behavior: No Zone of Indifference
-- ============================================================================

/-- MPAs lack a zone of indifference (@cite{beltrama-2025} §6.3, p. 199--200).

    The necessity standard provides a crisp boundary: an object either
    meets the minimum value for pursuit (MPA) or falls below it (¬MPA).
    The *neither MPA nor not-MPA* construction is defective because MPA
    has existential force (pursuit is possible in some accessible world)
    while its negation has universal force (no accessible world supports
    pursuit); combining these yields a contradiction.

    By contrast, *good*/*bad* are lexical contraries with separate
    distributional thresholds, permitting a gap region where an object
    fails to "stand out" with respect to either standard. -/
theorem mpa_no_indifference_zone :
    mpaProfile.zoneOfIndifference = false ∧
    goodProfile.zoneOfIndifference = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 9. Adjective Class: MPAs as a Novel Category
-- ============================================================================

/-- MPAs don't fit Kennedy's three-way classification. They share
    context-sensitivity with relative adjectives and crisp judgments
    with absolute adjectives, forming a genuinely hybrid category. -/
def decentClass : AdjectiveClass := .mildlyPositive

/-- MPAs are neither relative nor absolute in the Kennedy 2007 sense. -/
theorem mpa_not_relative :
    decentClass.isRelative = false := rfl

-- ============================================================================
-- § 10. Integration: Kennedy 2007 Licensing Pipeline
-- ============================================================================

open Core.Scale (LicensingPipeline)

/-- MPAs (lower-bounded scale) are licensed for degree modification by
    @cite{kennedy-2007}'s scale-structure licensing pipeline. This is
    consistent with MPAs combining with *barely* and moderate modifiers,
    while their resistance to *very*/*extremely* is pragmatic (§6.2),
    not structural. -/
theorem mpa_licensed_by_pipeline :
    LicensingPipeline.isLicensed decent.scaleType = true ∧
    LicensingPipeline.isLicensed acceptable.scaleType = true ∧
    LicensingPipeline.isLicensed adequate.scaleType = true := ⟨rfl, rfl, rfl⟩

/-- *good* is also licensed (same scale structure). The difference
    between MPAs and *good* is in standard type, not in structural
    licensing. -/
theorem good_also_licensed :
    LicensingPipeline.isLicensed good.scaleType = true := rfl

-- ============================================================================
-- § 11. Integration: Evaluative Valence
-- ============================================================================

open Core (EvaluativeValence)

/-- MPAs have positive evaluative valence: they denote a favorable
    (if mild) assessment. This connects to @cite{nouwen-2024}'s
    evaluative measure semantics. -/
def mpaValence : EvaluativeValence := .positive

/-- *good* shares positive valence with MPAs. -/
def goodValence : EvaluativeValence := .positive

/-- Both MPAs and *good* are positively evaluative, distinguishing
    them from neutral (*usual*) or negative (*terrible*) bases. -/
theorem mpa_good_same_valence :
    mpaValence = goodValence := rfl

-- ============================================================================
-- § 12. Integration: DegPType.sufficiency (*enough* parallel)
-- ============================================================================

open Semantics.Degree (DegPType)

/-- MPAs encode the same necessity component as *enough*
    (@cite{beltrama-2025} §5.3; Nadathur 2023): the minimum degree
    required for the complement/pursuit to be circumstantially possible.

    The parallel: "old enough to drink" ≈ "acceptable (for the purpose)".
    Both introduce a functional standard via a circumstantial modal base.
    The key difference: *enough* takes an overt complement clause while
    MPAs get their purpose from context (action-guidance). -/
def enoughParallel : DegPType := .sufficiency

-- ============================================================================
-- § 13. Integration: IE Divergence for Evaluative Predicates
-- ============================================================================

/-- Interpretive Economy maps lower-bounded → minEndpoint, but on the
    value scale THREE different standards coexist:

    1. *good*: contextual (distributional, like *tall*)
    2. MPAs: functional (necessity, like *enough*)
    3. MinSAAs (*wet*, *profitable*): minEndpoint (as IE predicts)

    This demonstrates that IE must be generalized: the **s** function
    can assign functional standards when the adjective's lexical semantics
    introduces practical commitments (@cite{beltrama-2025} §5.4, p. 195). -/
theorem ie_divergence_on_value_scale :
    interpretiveEconomy valueScaleBoundedness = .minEndpoint ∧
    goodStandard = .contextual ∧
    mpaStandard = .functional ∧
    minsaaStandard = .minEndpoint ∧
    goodStandard ≠ mpaStandard ∧
    mpaStandard ≠ minsaaStandard := by
  exact ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

end Beltrama2025
