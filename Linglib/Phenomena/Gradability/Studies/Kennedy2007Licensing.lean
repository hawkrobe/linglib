import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Scales.Scale
import Linglib.Core.PropertyDomain

/-!
# @cite{kennedy-2007} Adjective Licensing Bridge
@cite{kennedy-2007} @cite{kennedy-mcnally-2005}

Connects the abstract `adjMeasure` and `LicensingPipeline` algebra
(Core/Scale) to concrete Fragment entries (`tall`, `full`, `wet`, `dry`)
and Phenomena data (`closurePuzzle`, `completelyModifier`).

## Bridge Structure

1. **Fragment → DirectedMeasure**: each Fragment entry's `scaleType`
   determines a `DirectedMeasure`, whose `.licensed` field yields the
   licensing prediction.

2. **DirectedMeasure → Data**: the licensing prediction matches the
   empirical patterns recorded in `closurePuzzle` and `completelyModifier`.

3. **LicensingPipeline**: the same prediction is available through the
   universal `LicensingPipeline.isLicensed` interface, connecting
   adjective licensing to telicity, path shape, and mereological licensing.

-/

namespace Phenomena.Gradability.Kennedy2007

-- ════════════════════════════════════════════════════
-- Empirical Data (@cite{kennedy-2007})
-- ════════════════════════════════════════════════════

/--
Empirical pattern: Scalar adjective thresholds shift with comparison class.

The same individual can be "tall" relative to one class but "not tall"
relative to another. The threshold tracks statistical properties of
the comparison class (especially mean and variance).

Examples:
- 5'10" is tall for a jockey but not tall for a basketball player
- $500,000 is expensive for Atlanta but cheap for San Francisco

Source: @cite{kennedy-2007}, @cite{fara-2000}, @cite{lassiter-goodman-2017}
-/
structure ContextShiftDatum where
  /-- The adjective being used -/
  adjective : String
  /-- The individual/item being described -/
  individual : String
  /-- The value on the underlying scale (as string for flexibility) -/
  scaleValue : String
  /-- First comparison class -/
  comparisonClass1 : String
  /-- Second comparison class -/
  comparisonClass2 : String
  /-- Judgment in first class (true = adjective applies) -/
  judgmentInClass1 : Bool
  /-- Judgment in second class -/
  judgmentInClass2 : Bool
  deriving Repr

/-- Classic height example: 5'10" person. -/
def jockeyBasketball : ContextShiftDatum :=
  { adjective := "tall"
  , individual := "person X"
  , scaleValue := "5'10\""
  , comparisonClass1 := "jockeys"
  , comparisonClass2 := "basketball players"
  , judgmentInClass1 := true   -- tall for a jockey
  , judgmentInClass2 := false  -- not tall for a basketball player
  }

/-- House price example. -/
def atlantaSanFrancisco : ContextShiftDatum :=
  { adjective := "expensive"
  , individual := "house Y"
  , scaleValue := "$500,000"
  , comparisonClass1 := "houses in Atlanta"
  , comparisonClass2 := "houses in San Francisco"
  , judgmentInClass1 := true   -- expensive for Atlanta
  , judgmentInClass2 := false  -- not expensive for SF
  }

/-- Size example across orders of magnitude. -/
def microbePlanet : ContextShiftDatum :=
  { adjective := "big"
  , individual := "entity Z"
  , scaleValue := "10 micrometers"
  , comparisonClass1 := "microbes"
  , comparisonClass2 := "planets"
  , judgmentInClass1 := true   -- big for a microbe
  , judgmentInClass2 := false  -- definitely not big for a planet
  }

def contextShiftExamples : List ContextShiftDatum :=
  [jockeyBasketball, atlantaSanFrancisco, microbePlanet]

/--
Empirical pattern: Antonym pairs share a scale with reversed polarity.

"Tall" and "short" live on the same height scale but point in opposite
directions. This creates the "excluded middle gap" where neither applies
clearly (the borderline region).

Source: @cite{kennedy-2007}, @cite{lassiter-goodman-2017}
-/
structure AntonymDatum where
  /-- The positive adjective -/
  positive : String
  /-- The negative adjective -/
  negative : String
  /-- The underlying scale -/
  scale : String
  /-- Contradictory (A ≡ ¬B, no gap) or contrary (can both be false, gap). -/
  negationType : Core.NegationType
  /-- Example where positive applies -/
  positiveExample : String
  /-- Example where negative applies -/
  negativeExample : String
  /-- Example where neither clearly applies -/
  neitherExample : String
  deriving Repr

def tallShortAntonym : AntonymDatum :=
  { positive := "tall"
  , negative := "short"
  , scale := "height"
  , negationType := .contrary  -- both can be false
  , positiveExample := "7-footer is tall"
  , negativeExample := "5-footer is short"
  , neitherExample := "5'9\" person is neither clearly tall nor clearly short"
  }

def expensiveCheapAntonym : AntonymDatum :=
  { positive := "expensive"
  , negative := "cheap"
  , scale := "price"
  , negationType := .contrary
  , positiveExample := "$1M house is expensive"
  , negativeExample := "$50K house is cheap"
  , neitherExample := "$400K house is neither clearly expensive nor cheap"
  }

def antonymExamples : List AntonymDatum :=
  [tallShortAntonym, expensiveCheapAntonym]

/--
Data capturing Kennedy's adjective typology predictions.

Key diagnostic: behavior with degree modifiers
- RGA: "??slightly tall", "??completely tall" (odd)
- AGA-max: "slightly bent", "completely straight" (natural)
- AGA-min: "slightly wet", "??completely wet" (asymmetric)

Source: @cite{kennedy-2007} Section 3
-/
structure AdjectiveTypologyDatum where
  /-- The adjective -/
  adjective : String
  /-- Its classification -/
  classification : Semantics.Degree.AdjectiveClass
  /-- The underlying scale -/
  scale : String
  /-- Does it have a maximum endpoint? -/
  hasMaxEndpoint : Bool
  /-- Does it have a minimum endpoint? -/
  hasMinEndpoint : Bool
  /-- Natural with "slightly X"? -/
  naturalWithSlightly : Bool
  /-- Natural with "completely X"? -/
  naturalWithCompletely : Bool
  /-- Threshold shifts with comparison class? -/
  thresholdShifts : Bool
  deriving Repr

/-- "Tall" - prototypical relative gradable adjective. -/
def tallTypology : AdjectiveTypologyDatum :=
  { adjective := "tall"
  , classification := .relativeGradable
  , scale := "height"
  , hasMaxEndpoint := false
  , hasMinEndpoint := true  -- zero height, but not linguistically relevant
  , naturalWithSlightly := false  -- "??slightly tall"
  , naturalWithCompletely := false  -- "??completely tall"
  , thresholdShifts := true
  }

/-- "Full" - absolute maximum standard adjective. -/
def fullTypology : AdjectiveTypologyDatum :=
  { adjective := "full"
  , classification := .absoluteMaximum
  , scale := "fullness"
  , hasMaxEndpoint := true
  , hasMinEndpoint := true  -- empty
  , naturalWithSlightly := true   -- "slightly full" (= almost full)
  , naturalWithCompletely := true -- "completely full"
  , thresholdShifts := false
  }

/-- "Wet" - absolute minimum standard adjective. -/
def wetTypology : AdjectiveTypologyDatum :=
  { adjective := "wet"
  , classification := .absoluteMinimum
  , scale := "wetness"
  , hasMaxEndpoint := false  -- no clear maximum
  , hasMinEndpoint := true   -- zero wetness
  , naturalWithSlightly := true  -- "slightly wet"
  , naturalWithCompletely := false  -- "??completely wet"
  , thresholdShifts := false
  }

/-- "Straight" - absolute maximum standard adjective. -/
def straightTypology : AdjectiveTypologyDatum :=
  { adjective := "straight"
  , classification := .absoluteMaximum
  , scale := "straightness"
  , hasMaxEndpoint := true
  , hasMinEndpoint := true
  , naturalWithSlightly := true
  , naturalWithCompletely := true
  , thresholdShifts := false
  }

/-- "Bent" - absolute minimum standard adjective. -/
def bentTypology : AdjectiveTypologyDatum :=
  { adjective := "bent"
  , classification := .absoluteMinimum
  , scale := "bentness"
  , hasMaxEndpoint := true  -- maximally bent
  , hasMinEndpoint := true  -- straight (zero bentness)
  , naturalWithSlightly := true   -- "slightly bent"
  , naturalWithCompletely := false -- "??completely bent" (odd)
  , thresholdShifts := false
  }

def adjectiveTypologyExamples : List AdjectiveTypologyDatum :=
  [tallTypology, fullTypology, wetTypology, straightTypology, bentTypology]

/--
The key prediction: RGAs are context-sensitive, AGAs are not.

This is testable: change comparison class, see if threshold shifts.
- "tall for a basketball player" vs "tall for a jockey" - shifts
- "wet for a desert" vs "wet for a rainforest" - does NOT shift
-/
structure RGAvsAGAPrediction where
  rgaAdjective : String
  agaAdjective : String
  rgaShifts : Bool
  agaShifts : Bool
  rgaShiftExample : String
  agaNonShiftExample : String
  deriving Repr

def rgaVsAgaPrediction : RGAvsAGAPrediction :=
  { rgaAdjective := "tall"
  , agaAdjective := "wet"
  , rgaShifts := true
  , agaShifts := false
  , rgaShiftExample := "5'10\" is tall for a jockey, not tall for a basketball player"
  , agaNonShiftExample := "A damp cloth is wet whether comparing to deserts or rainforests"
  }

/--
Degree modifiers and their interactions with adjective types.

Key modifiers:
- Proportional: "half", "completely", "partially"
- Measure phrases: "6 feet tall", "3 degrees warmer"
- Intensifiers: "very", "extremely", "incredibly"
- Diminishers: "slightly", "somewhat", "a bit"

Source: @cite{kennedy-mcnally-2005}, @cite{burnett-2017}
-/
inductive DegreeModifierType where
  | proportional    -- half, completely, partially (require bounded scale)
  | measurePhrase   -- 6 feet tall (require dimensional scale)
  | intensifier     -- very, extremely (shift threshold up)
  | diminisher      -- slightly, somewhat (shift threshold down)
  deriving Repr, DecidableEq, BEq

/--
Data capturing degree modifier compatibility patterns.

The puzzle: Why can you say "completely full" but not "??completely tall"?

Answer: Proportional modifiers require a BOUNDED scale (endpoints).
- "Full" has a maximum → "completely full" works
- "Tall" has no maximum → "??completely tall" is odd

Source: @cite{kennedy-mcnally-2005}
-/
structure DegreeModifierDatum where
  modifier : String
  modifierType : DegreeModifierType
  worksWithRGA : Bool
  worksWithAGAMax : Bool
  worksWithAGAMin : Bool
  goodExample : String
  badExample : String
  deriving Repr

def completelyModifier : DegreeModifierDatum :=
  { modifier := "completely"
  , modifierType := .proportional
  , worksWithRGA := false    -- "??completely tall"
  , worksWithAGAMax := true  -- "completely full/straight"
  , worksWithAGAMin := false -- "??completely wet/bent"
  , goodExample := "The glass is completely full"
  , badExample := "??John is completely tall"
  }

def slightlyModifier : DegreeModifierDatum :=
  { modifier := "slightly"
  , modifierType := .diminisher
  , worksWithRGA := false    -- "??slightly tall"
  , worksWithAGAMax := true  -- "slightly less than full" → "slightly full"
  , worksWithAGAMin := true  -- "slightly wet"
  , goodExample := "The towel is slightly wet"
  , badExample := "??John is slightly tall"
  }

def veryModifier : DegreeModifierDatum :=
  { modifier := "very"
  , modifierType := .intensifier
  , worksWithRGA := true     -- "very tall"
  , worksWithAGAMax := true  -- "very full" (though less natural)
  , worksWithAGAMin := true  -- "very wet"
  , goodExample := "John is very tall"
  , badExample := "(all combinations are acceptable)"
  }

def halfModifier : DegreeModifierDatum :=
  { modifier := "half"
  , modifierType := .proportional
  , worksWithRGA := false    -- "??half tall"
  , worksWithAGAMax := true  -- "half full"
  , worksWithAGAMin := false -- "??half wet" (no clear midpoint)
  , goodExample := "The glass is half full"
  , badExample := "??John is half tall"
  }

def degreeModifierExamples : List DegreeModifierDatum :=
  [completelyModifier, slightlyModifier, veryModifier, halfModifier]

/--
The degree modifier puzzle: Why the distribution?

Formal constraint: Proportional modifiers require a CLOSED scale.
- Closed scale: has both minimum and maximum endpoints
- Open scale: missing at least one endpoint

This explains:
- "completely full" ✓ (fullness scale: empty to full)
- "??completely tall" ✗ (height scale: 0 to... what?)

Source: @cite{kennedy-mcnally-2005}, @cite{rotstein-winter-2004}
-/
structure ScaleClosurePuzzle where
  closedScaleAdj : String
  openScaleAdj : String
  modifier : String
  worksWithClosed : Bool
  worksWithOpen : Bool
  deriving Repr

def closurePuzzle : ScaleClosurePuzzle :=
  { closedScaleAdj := "full"
  , openScaleAdj := "tall"
  , modifier := "completely"
  , worksWithClosed := true
  , worksWithOpen := false
  }

end Phenomena.Gradability.Kennedy2007

-- ════════════════════════════════════════════════════
-- Licensing Bridge Theorems
-- ════════════════════════════════════════════════════

namespace Phenomena.Gradability.KennedyLicensingBridge

open Semantics.Lexical.Adjective
open Fragments.English.Predicates.Adjectival
open Core.Scale
open Phenomena.Gradability.Kennedy2007

-- ════════════════════════════════════════════════════
-- § 1. Fragment → DirectedMeasure Licensing
-- ════════════════════════════════════════════════════

/-- "tall" (open scale) → DirectedMeasure blocks degree modification. -/
theorem tall_blocks_completely {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ tall).licensed = false :=
  openAdj_blocked μ tall rfl

/-- "full" (closed scale) → DirectedMeasure licenses degree modification. -/
theorem full_licenses_completely {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ full).licensed = true :=
  closedAdj_licensed μ full rfl

/-- "wet" (lower-bounded) → DirectedMeasure licenses. -/
theorem wet_licensed {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ wet).licensed = true := by
  simp only [adjMeasure, DirectedMeasure.kennedyAdjective,
        DirectedMeasure.licensed, wet, Boundedness.isLicensed]

/-- "dry" (upper-bounded) → DirectedMeasure licenses. -/
theorem dry_licensed {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ dry).licensed = true := by
  simp only [adjMeasure, DirectedMeasure.kennedyAdjective,
        DirectedMeasure.licensed, dry, Boundedness.isLicensed]

-- ════════════════════════════════════════════════════
-- § 2. DirectedMeasure → Data Bridges
-- ════════════════════════════════════════════════════

/-- The closure puzzle is predicted by DirectedMeasure:
    closed-scale adjectives license "completely", open-scale ones don't.
    Matches `closurePuzzle.worksWithClosed` / `.worksWithOpen`. -/
theorem closurePuzzle_predicted {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ full).licensed = closurePuzzle.worksWithClosed ∧
    (adjMeasure μ tall).licensed = closurePuzzle.worksWithOpen := by
  exact ⟨closedAdj_licensed μ full rfl, openAdj_blocked μ tall rfl⟩

/-- "completely" works with AGA-max (closed) but not RGA (open).
    `adjMeasure` licensing matches `completelyModifier` fields. -/
theorem completely_distribution {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ full).licensed = completelyModifier.worksWithAGAMax ∧
    (adjMeasure μ tall).licensed = completelyModifier.worksWithRGA := by
  exact ⟨closedAdj_licensed μ full rfl, openAdj_blocked μ tall rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. LicensingPipeline Bridges
-- ════════════════════════════════════════════════════

/-- "tall" through the universal pipeline: open_ → blocked. -/
theorem adj_pipeline_tall :
    LicensingPipeline.isLicensed tall.scaleType = false := rfl

/-- "full" through the universal pipeline: closed → licensed. -/
theorem adj_pipeline_full :
    LicensingPipeline.isLicensed full.scaleType = true := rfl

/-- "wet" through the universal pipeline: lowerBounded → licensed. -/
theorem adj_pipeline_wet :
    LicensingPipeline.isLicensed wet.scaleType = true := rfl

/-- "dry" through the universal pipeline: upperBounded → licensed. -/
theorem adj_pipeline_dry :
    LicensingPipeline.isLicensed dry.scaleType = true := rfl

/-- Pipeline agrees with DirectedMeasure for all four test adjectives. -/
theorem pipeline_agrees_with_measure {max : Nat} {W : Type*} (μ : W → Degree max) :
    LicensingPipeline.isLicensed tall.scaleType = (adjMeasure μ tall).licensed ∧
    LicensingPipeline.isLicensed full.scaleType = (adjMeasure μ full).licensed ∧
    LicensingPipeline.isLicensed wet.scaleType = (adjMeasure μ wet).licensed ∧
    LicensingPipeline.isLicensed dry.scaleType = (adjMeasure μ dry).licensed := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [LicensingPipeline.isLicensed, LicensingPipeline.toBoundedness,
          adjMeasure, DirectedMeasure.kennedyAdjective, DirectedMeasure.licensed,
          tall, full, wet, dry, Boundedness.isLicensed]

-- ════════════════════════════════════════════════════
-- § 4. Scale Structure → Comparison Class Sensitivity
-- ════════════════════════════════════════════════════

/-! ### Two independent paths to the same prediction

@cite{kennedy-2007}'s scale structure and `PropertyDomain.requiresComparisonClass`
are two independent classifications that converge on the same prediction for
whether an adjective's standard depends on contextual domain information:

- **Scale-structure path** (@cite{kennedy-2007}): `scaleType → interpretiveEconomy
  → PositiveStandard → PositiveStandard.requiresComparisonClass`
  Open scale → contextual **s** → requires "the distribution of objects in some
  domain (a comparison class)" (Kennedy 2007, p. 42)
- **Domain path** (@cite{sedivy-etal-1999}): `dimension.domain →
  PropertyDomain.requiresComparisonClass`
  Size/evaluative/sensory domains → context-sensitive threshold

Note: Kennedy argues (§2.3, p. 16) that the comparison class is descriptively
real but NOT a semantic argument of *pos*. Our `requiresComparisonClass` tracks
whether contextual domain information is needed — compatible with Kennedy's
view that this information feeds into **s** contextually rather than as a
constituent of the logical form.

For every concrete Fragment adjective, the two paths agree. This convergence
is non-trivial: it reflects the empirical fact that open-scale adjectives
tend to belong to context-sensitive domains (size, evaluative), while
closed-scale adjectives tend to belong to context-insensitive domains (state). -/

open Semantics.Degree (interpretiveEconomy PositiveStandard)

/-- "tall": both paths predict CC-dependence. -/
theorem tall_cc_convergence :
    (interpretiveEconomy tall.scaleType).requiresComparisonClass = true ∧
    tall.dimension.domain.requiresComparisonClass = true :=
  ⟨rfl, rfl⟩

/-- "full": both paths predict CC-independence. -/
theorem full_no_cc_convergence :
    (interpretiveEconomy full.scaleType).requiresComparisonClass = false ∧
    full.dimension.domain.requiresComparisonClass = false :=
  ⟨rfl, rfl⟩

/-- "wet": both paths predict CC-independence
    (lower-bounded → endpoint standard; state domain). -/
theorem wet_no_cc_convergence :
    (interpretiveEconomy wet.scaleType).requiresComparisonClass = false ∧
    wet.dimension.domain.requiresComparisonClass = false :=
  ⟨rfl, rfl⟩

/-- "dry": both paths predict CC-independence
    (upper-bounded → endpoint standard; state domain). -/
theorem dry_no_cc_convergence :
    (interpretiveEconomy dry.scaleType).requiresComparisonClass = false ∧
    dry.dimension.domain.requiresComparisonClass = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. MPA Licensing (@cite{beltrama-2025})
-- ════════════════════════════════════════════════════

/-- MPAs (lower-bounded scale) are licensed by the pipeline, just like
    *wet*. Their resistance to *very*/*extremely* is pragmatic (conflicts
    with middling inference), not structural. -/
theorem mpa_licensed :
    LicensingPipeline.isLicensed decent.scaleType = true ∧
    LicensingPipeline.isLicensed acceptable.scaleType = true ∧
    LicensingPipeline.isLicensed adequate.scaleType = true := ⟨rfl, rfl, rfl⟩

/-- MPAs and *good* have the same scale-structure licensing status
    (both lower-bounded → licensed). Their difference is in standard
    type (functional vs contextual), not in structural licensing. -/
theorem mpa_good_same_licensing :
    LicensingPipeline.isLicensed decent.scaleType =
    LicensingPipeline.isLicensed good.scaleType := rfl

/-- IE path diverges for MPAs: lower-bounded → minEndpoint, but MPAs
    actually receive a functional standard. This is a genuine exception
    to Interpretive Economy, distinct from *good*'s exception. -/
theorem mpa_ie_exception :
    (interpretiveEconomy decent.scaleType) = .minEndpoint ∧
    (interpretiveEconomy decent.scaleType).requiresComparisonClass = false ∧
    -- But MPAs ARE context-sensitive (purpose-relative)
    decent.dimension.domain.requiresComparisonClass = true := ⟨rfl, rfl, rfl⟩

end Phenomena.Gradability.KennedyLicensingBridge
