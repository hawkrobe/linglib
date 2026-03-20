import Linglib.Core.PropertyDomain

/-
# Degree Phenomena: Empirical Patterns

Theory-neutral data about degree semantics across categories.
@cite{morzycki-2009}

## Scope

This module covers degree-related phenomena:
- **Scale structure**: Kennedy's adjective typology (RGA vs AGA)
- **Degree modifiers**: "completely", "slightly", "very", etc.
- **Context-sensitivity**: Threshold shifting with comparison class
- **Antonym behavior**: Tall/short, expensive/cheap
- **Nominal gradability**: Gradable nouns (idiot, fan, smoker)
- **Size adjective modification**: "big idiot", "huge fan"

For vagueness-specific phenomena (borderline cases, sorites, tolerance),
see `Gradability/Vagueness.lean`.

For evaluativity patterns, see `Gradability/Evaluativity.lean`.

## Insight

Scales (⟨warm, hot⟩, ⟨some, all⟩) are grounded in degree semantics:
"hot" is stronger than "warm" because it requires a higher degree threshold.

-/

namespace Phenomena.Gradability


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
Kennedy's adjective classification based on scale structure and standard type.

The key distinction:
- **Relative Gradable Adjectives (RGA)**: Standard varies with comparison class
  Examples: tall, expensive, big, old
- **Absolute Gradable Adjectives (AGA)**: Standard fixed by scale structure
  - Maximum standard: full, straight, closed, dry
  - Minimum standard: wet, bent, open, dirty

Source: @cite{kennedy-2007}, @cite{kennedy-mcnally-2005}
-/
inductive AdjectiveClass where
  | relativeGradable     -- tall, expensive, big (context-dependent threshold)
  | absoluteMaximum      -- full, straight, closed (threshold = max of scale)
  | absoluteMinimum      -- wet, bent, open (threshold = min of scale)
  | mildlyPositive       -- decent, acceptable, adequate (necessity standard, @cite{beltrama-2025})
  deriving Repr, DecidableEq, BEq

/-- Coarse 2-way classification: relative vs absolute.
    Collapses absoluteMaximum and absoluteMinimum. -/
def AdjectiveClass.isRelative : AdjectiveClass → Bool
  | .relativeGradable => true
  | _                 => false

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
  classification : AdjectiveClass
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

-- Theory Desiderata

/-!
## What a Theory of Degree Semantics Must Explain

### Adjectival Phenomena

1. **Scale structure**: RGA vs AGA distinction
   - RGAs have context-dependent thresholds
   - AGAs have scale-structure-determined thresholds

2. **Degree modifier distribution**:
   - "completely tall" ✗ vs "completely full" ✓
   - Proportional modifiers require closed scales

3. **Context-sensitivity**: Thresholds shift with comparison class
   - "tall for a jockey" vs "tall for a basketball player"

4. **Antonym behavior**: Contrary pairs share scales
   - tall/short, expensive/cheap

### Nominal Phenomena

5. **Degree readings exist**: "big idiot" can mean "very idiotic"

6. **Bigness Generalization**: Only positive-polarity size adjectives
   - "big/huge/enormous idiot" ✓
   - "small/tiny/little idiot" ✗ (degree reading)

7. **Position Generalization**: Only attributive position
   - "a big idiot" ✓ (degree reading)
   - "The idiot is big" ✗ (only size reading)

## Connection: Bigness Generalization ↔ Scale Structure

The Bigness Generalization follows from the same scale structure principles:
- Positive adjectives (big): upward monotonic on degree scale
  - min{d : big(d)} = θ_big (a substantive positive threshold)
- Negative adjectives (small): downward monotonic
  - min{d : small(d)} = d₀ (the scale minimum - vacuous!)

This parallels adjectival scale structure effects:
- Measure phrases: "6 feet tall" ✓ vs "6 feet short" ✗
- Proportional modifiers: "completely full" ✓ vs "completely tall" ✗
-/

end Phenomena.Gradability
