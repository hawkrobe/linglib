/-
# Degree Phenomena: Empirical Patterns

Theory-neutral data about degree semantics across categories.

## Scope

This module covers degree-related phenomena:
- **Scale structure**: Kennedy's adjective typology (RGA vs AGA)
- **Degree modifiers**: "completely", "slightly", "very", etc.
- **Context-sensitivity**: Threshold shifting with comparison class
- **Antonym behavior**: Tall/short, expensive/cheap
- **Nominal gradability**: Gradable nouns (idiot, fan, smoker)
- **Size adjective modification**: "big idiot", "huge fan"

For vagueness-specific phenomena (borderline cases, sorites, tolerance),
see `Phenomena/Vagueness/Data.lean`.

## Key Insight

Scales (⟨warm, hot⟩, ⟨some, all⟩) are grounded in degree semantics:
"hot" is stronger than "warm" because it requires a higher degree threshold.

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Kennedy, C. & McNally, L. (2005). Scale structure and degree modification.
- Morzycki, M. (2009). Degree modification of gradable nouns.
- Lassiter, D. & Goodman, N. (2017). Adjectival vagueness in a Bayesian model.
- Burnett, H. (2017). Gradability in Natural Language.
-/

namespace Phenomena.Degrees

-- ============================================================================
-- PART 1: Context-Sensitivity (Threshold Shifting)
-- ============================================================================

/--
Empirical pattern: Scalar adjective thresholds shift with comparison class.

The same individual can be "tall" relative to one class but "not tall"
relative to another. The threshold tracks statistical properties of
the comparison class (especially mean and variance).

Examples:
- 5'10" is tall for a jockey but not tall for a basketball player
- $500,000 is expensive for Atlanta but cheap for San Francisco

Source: Kennedy (2007), Fara (2000), Lassiter & Goodman (2017)
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

-- ============================================================================
-- PART 2: Antonym Behavior
-- ============================================================================

/--
Empirical pattern: Antonym pairs share a scale with reversed polarity.

"Tall" and "short" live on the same height scale but point in opposite
directions. This creates the "excluded middle gap" where neither applies
clearly (the borderline region).

Source: Kennedy (2007), Lassiter & Goodman (2017)
-/
structure AntonymDatum where
  /-- The positive adjective -/
  positive : String
  /-- The negative adjective -/
  negative : String
  /-- The underlying scale -/
  scale : String
  /-- Are they contradictories (A ≡ ¬B) or contraries (can both be false)? -/
  areContradictories : Bool
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
  , areContradictories := false  -- both can be false (contraries)
  , positiveExample := "7-footer is tall"
  , negativeExample := "5-footer is short"
  , neitherExample := "5'9\" person is neither clearly tall nor clearly short"
  }

def expensiveCheapAntonym : AntonymDatum :=
  { positive := "expensive"
  , negative := "cheap"
  , scale := "price"
  , areContradictories := false
  , positiveExample := "$1M house is expensive"
  , negativeExample := "$50K house is cheap"
  , neitherExample := "$400K house is neither clearly expensive nor cheap"
  }

def antonymExamples : List AntonymDatum :=
  [tallShortAntonym, expensiveCheapAntonym]

-- ============================================================================
-- PART 3: Kennedy (2007) Adjective Typology
-- ============================================================================

/--
Kennedy's adjective classification based on scale structure and standard type.

The key distinction:
- **Relative Gradable Adjectives (RGA)**: Standard varies with comparison class
  Examples: tall, expensive, big, old
- **Absolute Gradable Adjectives (AGA)**: Standard fixed by scale structure
  - Maximum standard: full, straight, closed, dry
  - Minimum standard: wet, bent, open, dirty

Source: Kennedy (2007), Kennedy & McNally (2005)
-/
inductive AdjectiveClass where
  | relativeGradable     -- tall, expensive, big (context-dependent threshold)
  | absoluteMaximum      -- full, straight, closed (threshold = max of scale)
  | absoluteMinimum      -- wet, bent, open (threshold = min of scale)
  deriving Repr, DecidableEq, BEq

/--
Data capturing Kennedy's adjective typology predictions.

Key diagnostic: behavior with degree modifiers
- RGA: "??slightly tall", "??completely tall" (odd)
- AGA-max: "slightly bent", "completely straight" (natural)
- AGA-min: "slightly wet", "??completely wet" (asymmetric)

Source: Kennedy (2007) Section 3
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

-- ============================================================================
-- PART 4: Degree Modifiers
-- ============================================================================

/--
Degree modifiers and their interactions with adjective types.

Key modifiers:
- Proportional: "half", "completely", "partially"
- Measure phrases: "6 feet tall", "3 degrees warmer"
- Intensifiers: "very", "extremely", "incredibly"
- Diminishers: "slightly", "somewhat", "a bit"

Source: Kennedy & McNally (2005), Burnett (2017)
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

Source: Kennedy & McNally (2005)
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
- "??completely tall" ✗ (height scale: 0 to ... what?)

Source: Kennedy & McNally (2005), Rotstein & Winter (2004)
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

-- ============================================================================
-- PART 5: Nominal Gradability - The Bigness Generalization
-- ============================================================================

/-- Size adjective polarity for degree readings -/
inductive SizePolarity where
  | positive  -- big, huge, enormous, tremendous
  | negative  -- small, tiny, little, slight
  deriving Repr, DecidableEq, BEq

/-- A bigness generalization datum: size adjective + degree reading availability -/
structure BignessGeneralizationDatum where
  sizeAdj : String
  polarity : SizePolarity
  degreeReadingAvailable : Bool
  sentence : String
  source : String

def bigIdiot : BignessGeneralizationDatum :=
  { sizeAdj := "big"
  , polarity := .positive
  , degreeReadingAvailable := true
  , sentence := "John is a big idiot"
  , source := "Morzycki 2009"
  }

def hugeFan : BignessGeneralizationDatum :=
  { sizeAdj := "huge"
  , polarity := .positive
  , degreeReadingAvailable := true
  , sentence := "Mary is a huge fan of Bach"
  , source := "Morzycki 2009"
  }

def enormousSmoker : BignessGeneralizationDatum :=
  { sizeAdj := "enormous"
  , polarity := .positive
  , degreeReadingAvailable := true
  , sentence := "He's an enormous smoker"
  , source := "Morzycki 2009"
  }

def smallIdiot : BignessGeneralizationDatum :=
  { sizeAdj := "small"
  , polarity := .negative
  , degreeReadingAvailable := false
  , sentence := "*John is a small idiot (meaning: low-degree idiot)"
  , source := "Morzycki 2009"
  }

def tinyFan : BignessGeneralizationDatum :=
  { sizeAdj := "tiny"
  , polarity := .negative
  , degreeReadingAvailable := false
  , sentence := "*Mary is a tiny fan (meaning: low-enthusiasm fan)"
  , source := "Morzycki 2009"
  }

def littleSmoker : BignessGeneralizationDatum :=
  { sizeAdj := "little"
  , polarity := .negative
  , degreeReadingAvailable := false
  , sentence := "*He's a little smoker (meaning: smokes little)"
  , source := "Morzycki 2009"
  }

def slightExaggeration : BignessGeneralizationDatum :=
  { sizeAdj := "slight"
  , polarity := .negative
  , degreeReadingAvailable := true  -- Exception!
  , sentence := "That's a slight exaggeration"
  , source := "Morzycki 2009"
  }

def bignessExamples : List BignessGeneralizationDatum :=
  [bigIdiot, hugeFan, enormousSmoker, smallIdiot, tinyFan, littleSmoker, slightExaggeration]

-- ============================================================================
-- PART 6: Position Generalization
-- ============================================================================

/-- Position generalization datum: attributive vs predicative -/
structure PositionGeneralizationDatum where
  noun : String
  sizeAdj : String
  position : String  -- "attributive" or "predicative"
  degreeReadingAvailable : Bool
  sentence : String
  source : String

def bigIdiotAttributive : PositionGeneralizationDatum :=
  { noun := "idiot"
  , sizeAdj := "big"
  , position := "attributive"
  , degreeReadingAvailable := true
  , sentence := "John is a big idiot"
  , source := "Morzycki 2009"
  }

def bigIdiotPredicative : PositionGeneralizationDatum :=
  { noun := "idiot"
  , sizeAdj := "big"
  , position := "predicative"
  , degreeReadingAvailable := false
  , sentence := "The idiot is big (*meaning: has high idiocy)"
  , source := "Morzycki 2009"
  }

def positionExamples : List PositionGeneralizationDatum :=
  [bigIdiotAttributive, bigIdiotPredicative]

-- ============================================================================
-- PART 7: Gradable Noun Scale Types
-- ============================================================================

/-- Types of nominal scales (de Vries 2010) -/
inductive NominalScaleType where
  | evaluative  -- idiot, genius (quality judgment)
  | enthusiasm  -- fan, lover, supporter (degree of devotion)
  | frequency   -- smoker, drinker (how often)
  | intensity   -- liar, cheat (how extremely)
  deriving Repr, DecidableEq, BEq

/-- Gradable noun examples by scale type -/
structure GradableNounExample where
  noun : String
  scaleType : NominalScaleType
  degreeAdjectives : List String
  sentence : String
  source : String

def idiotExample : GradableNounExample :=
  { noun := "idiot"
  , scaleType := .evaluative
  , degreeAdjectives := ["big", "huge", "complete", "total"]
  , sentence := "a big/huge/complete/total idiot"
  , source := "Morzycki 2009"
  }

def fanExample : GradableNounExample :=
  { noun := "fan"
  , scaleType := .enthusiasm
  , degreeAdjectives := ["big", "huge", "enormous"]
  , sentence := "a big/huge/enormous fan"
  , source := "Morzycki 2009"
  }

def smokerExample : GradableNounExample :=
  { noun := "smoker"
  , scaleType := .frequency
  , degreeAdjectives := ["big", "heavy"]
  , sentence := "a big/heavy smoker"
  , source := "Morzycki 2009"
  }

def liarExample : GradableNounExample :=
  { noun := "liar"
  , scaleType := .intensity
  , degreeAdjectives := ["big", "huge", "terrible"]
  , sentence := "a big/huge/terrible liar"
  , source := "Morzycki 2009"
  }

def gradableNounExamples : List GradableNounExample :=
  [idiotExample, fanExample, smokerExample, liarExample]

-- ============================================================================
-- PART 8: Nominal Comparison
-- ============================================================================

/-- Nouns can be compared like adjectives when gradable -/
structure NominalComparisonDatum where
  noun : String
  comparativeForm : String
  sentence : String
  acceptable : Bool
  source : String

def moreOfAnIdiot : NominalComparisonDatum :=
  { noun := "idiot"
  , comparativeForm := "more of an N"
  , sentence := "John is more of an idiot than Bill"
  , acceptable := true
  , source := "Morzycki 2009"
  }

def biggerIdiotComparison : NominalComparisonDatum :=
  { noun := "idiot"
  , comparativeForm := "bigger N"
  , sentence := "John is a bigger idiot than Bill"
  , acceptable := true
  , source := "Morzycki 2009"
  }

def nominalComparisonExamples : List NominalComparisonDatum :=
  [moreOfAnIdiot, biggerIdiotComparison]

-- ============================================================================
-- PART 9: Cross-linguistic Evidence
-- ============================================================================

/-- The Bigness Generalization holds cross-linguistically -/
structure CrossLinguisticDatum where
  language : String
  sizeAdj : String
  polarity : SizePolarity
  degreeReadingAvailable : Bool
  translation : String
  source : String

def germanGrossIdiot : CrossLinguisticDatum :=
  { language := "German"
  , sizeAdj := "groß"
  , polarity := .positive
  , degreeReadingAvailable := true
  , translation := "ein großer Idiot"
  , source := "Morzycki 2009"
  }

def germanKleinIdiot : CrossLinguisticDatum :=
  { language := "German"
  , sizeAdj := "klein"
  , polarity := .negative
  , degreeReadingAvailable := false
  , translation := "*ein kleiner Idiot (degree reading)"
  , source := "Morzycki 2009"
  }

def crossLinguisticExamples : List CrossLinguisticDatum :=
  [germanGrossIdiot, germanKleinIdiot]

-- ============================================================================
-- Theory Desiderata
-- ============================================================================

/-!
## What a Theory of Degree Semantics Must Explain

### Adjectival Phenomena

1. **Scale structure**: RGA vs AGA distinction (Kennedy 2007)
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

end Phenomena.Degrees
