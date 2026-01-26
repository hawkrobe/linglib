/-
# Vagueness: Empirical Data and Theoretical Puzzles

Theory-neutral empirical patterns and formal puzzles for vague predicates.

## Phenomena Covered

1. **Context-Sensitivity**: Thresholds shift based on comparison class
2. **Borderline Cases**: Intermediate judgments for middle values
3. **Sorites Paradox**: Acceptance of individual premises, rejection of conclusion
4. **Adjective Typology**: RGA vs AGA, maximum vs minimum standard (Kennedy 2007)
5. **Degree Modifiers**: "very", "slightly", "completely" etc.
6. **Higher-Order Vagueness**: Borderline cases of borderline cases
7. **Penumbral Connections**: Logical relationships in borderline region
8. **Tolerance Principle**: The key sorites ingredient

## Key References

- Kamp, H. (1975). Two theories about adjectives.
- Klein, E. (1980). A semantics for positive and comparative adjectives.
- Fine, K. (1975). Vagueness, truth and logic.
- Williamson, T. (1994). Vagueness.
- Kennedy, C. (2007). Vagueness and grammar.
- Edgington, D. (1997). Vagueness by degrees.
- Fara, D. G. (2000). Shifting sands: An interest-relative theory of vagueness.
- Lassiter, D. & Goodman, N. (2017). Adjectival vagueness in a Bayesian model.
- Burnett, H. (2017). Gradability in Natural Language.
-/

namespace Phenomena.Vagueness

-- ============================================================================
-- PART 1: Context-Sensitivity Data
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

/--
Classic height example: 5'10" person.
Source: Lassiter & Goodman (2017), Kennedy (2007)
-/
def jockeyBasketball : ContextShiftDatum :=
  { adjective := "tall"
  , individual := "person X"
  , scaleValue := "5'10\""
  , comparisonClass1 := "jockeys"
  , comparisonClass2 := "basketball players"
  , judgmentInClass1 := true   -- tall for a jockey
  , judgmentInClass2 := false  -- not tall for a basketball player
  }

/--
House price example.
Source: Lassiter & Goodman (2017) Section 1
-/
def atlantaSanFrancisco : ContextShiftDatum :=
  { adjective := "expensive"
  , individual := "house Y"
  , scaleValue := "$500,000"
  , comparisonClass1 := "houses in Atlanta"
  , comparisonClass2 := "houses in San Francisco"
  , judgmentInClass1 := true   -- expensive for Atlanta
  , judgmentInClass2 := false  -- not expensive for SF
  }

/--
Size example across orders of magnitude.
Source: Kennedy (2007)
-/
def microbePlanet : ContextShiftDatum :=
  { adjective := "big"
  , individual := "entity Z"
  , scaleValue := "10 micrometers"
  , comparisonClass1 := "microbes"
  , comparisonClass2 := "planets"
  , judgmentInClass1 := true   -- big for a microbe
  , judgmentInClass2 := false  -- definitely not big for a planet
  }

/--
All context-shift examples.
-/
def contextShiftExamples : List ContextShiftDatum :=
  [jockeyBasketball, atlantaSanFrancisco, microbePlanet]

-- ============================================================================
-- PART 2: Borderline Cases Data
-- ============================================================================

/--
Empirical pattern: Borderline cases elicit hedging and uncertainty.

For individuals near the inferred threshold:
- Speakers hedge or refuse to answer
- Judgments show high variance across informants
- Neither "A" nor "not A" feels fully appropriate

Source: Lassiter & Goodman (2017) Section 1, Kennedy (2007)
-/
structure BorderlineDatum where
  /-- The adjective -/
  adjective : String
  /-- Description of the context/comparison class -/
  context : String
  /-- Clear positive case (definitely A) -/
  clearPositive : String
  /-- Clear positive value -/
  clearPositiveValue : String
  /-- Clear negative case (definitely not A) -/
  clearNegative : String
  /-- Clear negative value -/
  clearNegativeValue : String
  /-- Borderline case -/
  borderline : String
  /-- Borderline value -/
  borderlineValue : String
  deriving Repr

/--
House price borderline example.
Source: Lassiter & Goodman (2017) Section 1, Example (1)
-/
def expensiveHouse : BorderlineDatum :=
  { adjective := "expensive"
  , context := "Neighborhood where most houses cost $300,000-$600,000"
  , clearPositive := "Williams' house"
  , clearPositiveValue := "$1,000,000"
  , clearNegative := "Clarks' house"
  , clearNegativeValue := "$75,000"
  , borderline := "Jacobsons' house"
  , borderlineValue := "$475,000"
  }

/--
Height borderline example.
Source: Constructed from Lassiter & Goodman (2017) model
-/
def tallPerson : BorderlineDatum :=
  { adjective := "tall"
  , context := "Adult American men (mean ~5'9\", SD ~3\")"
  , clearPositive := "Andre the Giant"
  , clearPositiveValue := "7'4\""
  , clearNegative := "Danny DeVito"
  , clearNegativeValue := "4'10\""
  , borderline := "Average man"
  , borderlineValue := "5'10\""
  }

/--
All borderline examples.
-/
def borderlineExamples : List BorderlineDatum :=
  [expensiveHouse, tallPerson]

-- ============================================================================
-- PART 3: Sorites Paradox Data
-- ============================================================================

/--
Empirical pattern: The sorites paradox.

Given:
1. A clearly Adj individual (premise 1)
2. A tolerance principle: "If x is Adj and y is ε smaller, then y is Adj" (premise 2)
3. Iterated application leads to a clearly non-Adj individual (conclusion)

Empirical observations:
- People accept premise 1 (the clear case)
- People accept individual instances of premise 2 (each step seems valid)
- People reject the conclusion (the absurd case)
- People show gradient acceptance as cases approach the threshold

Source: Edgington (1997), Lassiter & Goodman (2017) Section 5
-/
structure SoritesDatum where
  /-- The adjective -/
  adjective : String
  /-- The underlying scale description -/
  scale : String
  /-- The tolerance gap (ε) -/
  toleranceGap : String
  /-- Clear positive case -/
  clearPositive : String
  /-- Clear positive value -/
  positiveValue : String
  /-- Clear negative case -/
  clearNegative : String
  /-- Clear negative value -/
  negativeValue : String
  /-- Number of steps in the sorites -/
  numSteps : Nat
  /-- Do people accept premise 1? -/
  acceptPremise1 : Bool
  /-- Do people accept individual tolerance steps? -/
  acceptToleranceSteps : Bool
  /-- Do people accept the conclusion? -/
  acceptConclusion : Bool
  deriving Repr

/--
Classic tall sorites.
Source: Edgington (1997), Lassiter & Goodman (2017) Section 5
-/
def tallSorites : SoritesDatum :=
  { adjective := "tall"
  , scale := "height"
  , toleranceGap := "1 mm"
  , clearPositive := "Andre the Giant (7'4\")"
  , positiveValue := "7'4\""
  , clearNegative := "Danny DeVito (4'10\")"
  , negativeValue := "4'10\""
  , numSteps := 762  -- ~30 inches = 762 mm
  , acceptPremise1 := true
  , acceptToleranceSteps := true  -- each individual step accepted
  , acceptConclusion := false     -- paradoxical!
  }

/--
Heap sorites (the original).
Source: Eubulides of Miletus (4th c. BCE), Edgington (1997)
-/
def heapSorites : SoritesDatum :=
  { adjective := "heap"
  , scale := "number of grains"
  , toleranceGap := "1 grain"
  , clearPositive := "10,000 grains"
  , positiveValue := "10000"
  , clearNegative := "1 grain"
  , negativeValue := "1"
  , numSteps := 9999
  , acceptPremise1 := true
  , acceptToleranceSteps := true
  , acceptConclusion := false
  }

/--
Expensive sorites.
Source: Lassiter & Goodman (2017) Section 1
-/
def expensiveSorites : SoritesDatum :=
  { adjective := "expensive"
  , scale := "price"
  , toleranceGap := "$1"
  , clearPositive := "$10,000,000 house"
  , positiveValue := "10000000"
  , clearNegative := "$1 house"
  , negativeValue := "1"
  , numSteps := 9999999
  , acceptPremise1 := true
  , acceptToleranceSteps := true
  , acceptConclusion := false
  }

/--
All sorites examples.
-/
def soritesExamples : List SoritesDatum :=
  [tallSorites, heapSorites, expensiveSorites]

-- ============================================================================
-- PART 4: Antonym Behavior Data
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

/--
Tall/short antonym pair.
Source: Kennedy (2007), Lassiter & Goodman (2017)
-/
def tallShort : AntonymDatum :=
  { positive := "tall"
  , negative := "short"
  , scale := "height"
  , areContradictories := false  -- both can be false (contraries)
  , positiveExample := "7-footer is tall"
  , negativeExample := "5-footer is short"
  , neitherExample := "5'9\" person is neither clearly tall nor clearly short"
  }

/--
Expensive/cheap antonym pair.
Source: Kennedy (2007)
-/
def expensiveCheap : AntonymDatum :=
  { positive := "expensive"
  , negative := "cheap"
  , scale := "price"
  , areContradictories := false
  , positiveExample := "$1M house is expensive"
  , negativeExample := "$50K house is cheap"
  , neitherExample := "$400K house is neither clearly expensive nor cheap"
  }

/--
All antonym examples.
-/
def antonymExamples : List AntonymDatum :=
  [tallShort, expensiveCheap]

-- ============================================================================
-- PART 5: Kennedy (2007) Adjective Typology
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
  deriving Repr, DecidableEq

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

/--
"Tall" - prototypical relative gradable adjective.

- Scale has no inherent endpoints
- Threshold shifts with comparison class
- Odd with "completely" and "slightly"

Source: Kennedy (2007)
-/
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

/--
"Full" - absolute maximum standard adjective.

- Scale has maximum endpoint (completely full)
- Threshold IS the maximum
- "Slightly full" ≈ "not quite full" (natural)
- "Completely full" is natural

Source: Kennedy (2007)
-/
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

/--
"Wet" - absolute minimum standard adjective.

- Scale has minimum endpoint (any wetness at all)
- Threshold IS the minimum (any wetness counts)
- "Slightly wet" is natural
- "??Completely wet" is odd (no natural maximum)

Source: Kennedy (2007)
-/
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

/--
"Straight" - absolute maximum standard adjective.

- Scale endpoints: perfectly straight (max) to maximally bent (min)
- Standard = maximum (any deviation counts as "not straight")
- "Slightly straight" ≈ "almost straight" (natural)
- "Completely straight" is natural

Source: Kennedy (2007)
-/
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

/--
"Bent" - absolute minimum standard adjective.

The antonym of "straight". Any deviation from straight counts as bent.

Source: Kennedy (2007)
-/
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

Source: Kennedy (2007), Section 4
-/
structure RGAvsAGAPrediction where
  /-- Example RGA adjective -/
  rgaAdjective : String
  /-- Example AGA adjective -/
  agaAdjective : String
  /-- Does RGA threshold shift with class? -/
  rgaShifts : Bool
  /-- Does AGA threshold shift with class? -/
  agaShifts : Bool
  /-- Example of RGA shift -/
  rgaShiftExample : String
  /-- Example of AGA non-shift -/
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
-- PART 6: Degree Modifiers
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
  deriving Repr, DecidableEq

/--
Data capturing degree modifier compatibility patterns.

The puzzle: Why can you say "completely full" but not "??completely tall"?

Answer: Proportional modifiers require a BOUNDED scale (endpoints).
- "Full" has a maximum → "completely full" works
- "Tall" has no maximum → "??completely tall" is odd

Source: Kennedy & McNally (2005)
-/
structure DegreeModifierDatum where
  /-- The modifier -/
  modifier : String
  /-- The modifier type -/
  modifierType : DegreeModifierType
  /-- Works with RGA (tall, big)? -/
  worksWithRGA : Bool
  /-- Works with AGA-max (full, straight)? -/
  worksWithAGAMax : Bool
  /-- Works with AGA-min (wet, bent)? -/
  worksWithAGAMin : Bool
  /-- Example of good combination -/
  goodExample : String
  /-- Example of bad combination -/
  badExample : String
  deriving Repr

/--
"Completely" - requires maximum endpoint.

Source: Kennedy & McNally (2005)
-/
def completelyModifier : DegreeModifierDatum :=
  { modifier := "completely"
  , modifierType := .proportional
  , worksWithRGA := false    -- "??completely tall"
  , worksWithAGAMax := true  -- "completely full/straight"
  , worksWithAGAMin := false -- "??completely wet/bent"
  , goodExample := "The glass is completely full"
  , badExample := "??John is completely tall"
  }

/--
"Slightly" - requires deviation from standard.

- For AGA-max: "slightly" below maximum (natural)
- For AGA-min: "slightly" above minimum (natural)
- For RGA: "slightly" is odd because no clear reference point

Source: Kennedy & McNally (2005)
-/
def slightlyModifier : DegreeModifierDatum :=
  { modifier := "slightly"
  , modifierType := .diminisher
  , worksWithRGA := false    -- "??slightly tall"
  , worksWithAGAMax := true  -- "slightly less than full" → "slightly full"
  , worksWithAGAMin := true  -- "slightly wet"
  , goodExample := "The towel is slightly wet"
  , badExample := "??John is slightly tall"
  }

/--
"Very" - works broadly as an intensifier.

Unlike proportional modifiers, "very" doesn't require scale endpoints.
It shifts the threshold toward the relevant extreme.

Source: Kennedy & McNally (2005)
-/
def veryModifier : DegreeModifierDatum :=
  { modifier := "very"
  , modifierType := .intensifier
  , worksWithRGA := true     -- "very tall"
  , worksWithAGAMax := true  -- "very full" (though less natural)
  , worksWithAGAMin := true  -- "very wet"
  , goodExample := "John is very tall"
  , badExample := "(all combinations are acceptable)"
  }

/--
"Half" - requires bounded scale with midpoint.

Source: Kennedy & McNally (2005)
-/
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
  /-- Closed-scale adjective -/
  closedScaleAdj : String
  /-- Open-scale adjective -/
  openScaleAdj : String
  /-- Proportional modifier -/
  modifier : String
  /-- Works with closed scale? -/
  worksWithClosed : Bool
  /-- Works with open scale? -/
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
-- PART 7: Higher-Order Vagueness
-- ============================================================================

/--
The problem of higher-order vagueness.

If "tall" has borderline cases, what about "borderline tall"?
Is there a SHARP boundary between "borderline tall" and "clearly tall"?

- First-order vagueness: borderline cases of "tall"
- Second-order vagueness: borderline cases of "borderline tall"
- Third-order vagueness: borderline cases of "borderline borderline tall"
- ... and so on

This threatens any theory that posits sharp boundaries ANYWHERE.

Source: Fine (1975), Williamson (1994), Raffman (2014)
-/
structure HigherOrderVaguenessData where
  /-- The base predicate -/
  basePredicate : String
  /-- Description of clear positive case -/
  clearlyPositive : String
  /-- Description of first-order borderline -/
  borderline : String
  /-- Description of clear negative case -/
  clearlyNegative : String
  /-- Is there a sharp boundary between clearly-P and borderline-P? -/
  sharpClearlyBorderline : Bool
  /-- Is there a sharp boundary between borderline-P and clearly-not-P? -/
  sharpBorderlineNot : Bool
  /-- Does the pattern iterate to higher orders? -/
  iteratesUpward : Bool
  deriving Repr

/--
Higher-order vagueness for "tall".

Consider heights: 5'0", 5'6", 5'9", 6'0", 6'6", 7'0"

- 7'0": clearly tall (first-order)
- 5'0": clearly not tall (first-order)
- 5'9": borderline tall (first-order)

But what about 6'3"? Is it:
- Clearly tall?
- Borderline tall?
- Borderline "borderline tall"? (second-order)

The problem: wherever we draw the line, it seems arbitrary.

Source: Williamson (1994) Chapter 5
-/
def tallHigherOrder : HigherOrderVaguenessData :=
  { basePredicate := "tall"
  , clearlyPositive := "7'0\" is clearly tall"
  , borderline := "5'9\" is borderline tall"
  , clearlyNegative := "5'0\" is clearly not tall"
  , sharpClearlyBorderline := false  -- Puzzle: is 6'3\" clearly tall or borderline?
  , sharpBorderlineNot := false      -- Puzzle: is 5'6\" borderline or clearly not?
  , iteratesUpward := true           -- If no sharp boundary, problem repeats
  }

def higherOrderExamples : List HigherOrderVaguenessData := [tallHigherOrder]

/--
The "definitely" operator and higher-order vagueness.

If "Definitely tall" means "clearly tall" (not borderline), then:
- "Definitely tall" should have sharper boundaries than "tall"
- But "definitely" is ITSELF vague!
- So we get: "borderline definitely tall"

Iterating: "definitely definitely tall", etc.

Source: Fine (1975), Williamson (1994)
-/
structure DefinitelyOperatorData where
  /-- Base predicate -/
  predicate : String
  /-- Does "definitely P" eliminate borderline cases? -/
  eliminatesBorderline : Bool
  /-- Is "definitely" itself vague? -/
  definitelyIsVague : Bool
  /-- Can we have "borderline definitely P"? -/
  borderlineDefinitely : Bool
  /-- Does iteration help? (definitely definitely P) -/
  iterationHelps : Bool
  deriving Repr

def definitelyOperator : DefinitelyOperatorData :=
  { predicate := "tall"
  , eliminatesBorderline := true   -- that's the intent
  , definitelyIsVague := true      -- the problem!
  , borderlineDefinitely := true   -- so this is possible
  , iterationHelps := false        -- problem just moves up
  }

-- ============================================================================
-- PART 8: Penumbral Connections
-- ============================================================================

/--
Penumbral connections: logical relationships that hold even in borderline cases.

Even if we don't know whether John is tall:
- "John is tall ∨ John is not tall" is TRUE (excluded middle)
- "John is tall ∧ John is not tall" is FALSE (non-contradiction)
- If John = 5'9" and Mary = 5'9", then "John is tall ↔ Mary is tall" (same-height)

These are "penumbral truths" - true in the borderline region.

Supervaluationism: true iff true on ALL precisifications.
Degree theories: must explain why these have degree 1.

Source: Fine (1975), Keefe (2000)
-/
structure PenumbralConnectionData where
  /-- Description of the connection -/
  connectionName : String
  /-- Formal statement -/
  formalStatement : String
  /-- Is this always true, even in borderline cases? -/
  alwaysTrue : Bool
  /-- Example with borderline case -/
  borderlineExample : String
  /-- Does supervaluationism capture this? -/
  supervaluationismCaptures : Bool
  /-- Does degree theory capture this? -/
  degreeTheoryCaptures : Bool
  deriving Repr

/--
Excluded middle: P ∨ ¬P holds even when P is vague.

Even if we can't say whether "5'9\" John is tall":
- "John is tall or John is not tall" seems TRUE

Challenge for 3-valued logic: if P = 1/2, then P ∨ ¬P = 1/2 ≠ 1

Source: Fine (1975)
-/
def excludedMiddle : PenumbralConnectionData :=
  { connectionName := "Excluded Middle"
  , formalStatement := "∀x. Tall(x) ∨ ¬Tall(x)"
  , alwaysTrue := true
  , borderlineExample := "John is 5'9\". 'John is tall or John is not tall' is TRUE"
  , supervaluationismCaptures := true   -- true on all precisifications
  , degreeTheoryCaptures := false       -- 0.5 ∨ 0.5 = 0.5 ≠ 1 (with standard ∨)
  }

/--
Non-contradiction: ¬(P ∧ ¬P) holds even when P is vague.

"John is tall and John is not tall" is FALSE, even for borderline John.

Source: Fine (1975)
-/
def nonContradiction : PenumbralConnectionData :=
  { connectionName := "Non-Contradiction"
  , formalStatement := "∀x. ¬(Tall(x) ∧ ¬Tall(x))"
  , alwaysTrue := true
  , borderlineExample := "John is 5'9\". 'John is tall and not tall' is FALSE"
  , supervaluationismCaptures := true
  , degreeTheoryCaptures := false  -- 0.5 ∧ 0.5 = 0.5 ≠ 0
  }

/--
Same-height connection: equally tall individuals have same tallness status.

If John and Mary are exactly the same height:
- "John is tall ↔ Mary is tall" is TRUE
- Even if both are borderline!

This rules out arbitrary precisifications that treat them differently.

Source: Fine (1975)
-/
def sameHeightConnection : PenumbralConnectionData :=
  { connectionName := "Same-Height Equivalence"
  , formalStatement := "∀x y. Height(x) = Height(y) → (Tall(x) ↔ Tall(y))"
  , alwaysTrue := true
  , borderlineExample := "John and Mary are both 5'9\". 'John is tall iff Mary is tall' is TRUE"
  , supervaluationismCaptures := true  -- all precisifications respect this
  , degreeTheoryCaptures := true       -- same degree → same truth value
  }

/--
Comparative entailment: "taller than" entails relative tallness.

If John is taller than Mary and Mary is tall, then John is tall.
Contrapositively: if John is not tall and John is taller than Mary, Mary is not tall.

Source: Kennedy (2007)
-/
def comparativeEntailment : PenumbralConnectionData :=
  { connectionName := "Comparative Entailment"
  , formalStatement := "∀x y. Taller(x, y) ∧ Tall(y) → Tall(x)"
  , alwaysTrue := true
  , borderlineExample := "If 6'0\" John is taller than 5'9\" Mary, and Mary is tall, John is tall"
  , supervaluationismCaptures := true
  , degreeTheoryCaptures := true
  }

def penumbralExamples : List PenumbralConnectionData :=
  [excludedMiddle, nonContradiction, sameHeightConnection, comparativeEntailment]

-- ============================================================================
-- PART 9: Tolerance Principle and Sorites
-- ============================================================================

/--
The tolerance principle: the key ingredient in sorites paradoxes.

Tolerance: If x is F and y differs from x by only a tiny amount,
           then y is also F.

This seems TRUE for vague predicates:
- 1mm can't make the difference between tall and not-tall
- $1 can't make the difference between expensive and not-expensive
- 1 grain can't make the difference between heap and not-heap

But iterated application leads to absurdity (the sorites).

Source: Wright (1976), Fara (2000)
-/
structure TolerancePrincipleData where
  /-- The vague predicate -/
  predicate : String
  /-- The underlying scale -/
  scale : String
  /-- The tolerance margin (ε) -/
  toleranceMargin : String
  /-- Does each individual step seem acceptable? -/
  individualStepAcceptable : Bool
  /-- Does iterated application lead to absurdity? -/
  iterationAbsurd : Bool
  /-- Proposed explanation -/
  proposedResolution : String
  deriving Repr

/--
Height tolerance: 1mm can't matter for tallness.

Intuition: "If John (5'10\") is tall, then someone 1mm shorter is also tall"

But 762 such steps takes us from clearly tall to clearly not tall.

Source: Wright (1976)
-/
def heightTolerance : TolerancePrincipleData :=
  { predicate := "tall"
  , scale := "height"
  , toleranceMargin := "1 mm"
  , individualStepAcceptable := true
  , iterationAbsurd := true
  , proposedResolution := "Various: epistemicism, degree theory, supervaluationism, contextualism"
  }

/--
Price tolerance: $1 can't matter for expensiveness.

Source: Lassiter & Goodman (2017)
-/
def priceTolerance : TolerancePrincipleData :=
  { predicate := "expensive"
  , scale := "price"
  , toleranceMargin := "$1"
  , individualStepAcceptable := true
  , iterationAbsurd := true
  , proposedResolution := "Threshold uncertainty makes each step PROBABLY but not CERTAINLY acceptable"
  }

def toleranceExamples : List TolerancePrincipleData :=
  [heightTolerance, priceTolerance]

/--
Probabilistic sorites analysis (Edgington 1997, Lassiter & Goodman 2017).

Key insight: Each tolerance step is HIGHLY PROBABLE, not certain.

Let P(step) = 0.99 (each step is 99% acceptable)
After N steps: P(all steps) = 0.99^N

For N = 762 (mm from 7'4\" to 4'10\"):
0.99^762 ≈ 0.0005 (extremely unlikely!)

The paradox dissolves: the argument is valid but UNSOUND.
Each premise is PROBABLY true, but the conjunction is PROBABLY false.

Source: Edgington (1997), Lassiter & Goodman (2017) Section 5
-/
structure ProbabilisticSoritesData where
  /-- The predicate -/
  predicate : String
  /-- Probability of single tolerance step being valid -/
  singleStepProbability : Float
  /-- Number of steps in the sorites -/
  numSteps : Nat
  /-- Cumulative probability of all steps -/
  cumulativeProbability : Float
  /-- Is premise 1 (clear case) accepted? -/
  premise1Accepted : Bool
  /-- Is each individual tolerance step accepted? -/
  eachStepAccepted : Bool
  /-- Is the full argument accepted? -/
  fullArgumentAccepted : Bool
  deriving Repr

/--
Probabilistic analysis of tall sorites.

Each 1mm step: P ≈ 0.99
762 steps: P ≈ 0.99^762 ≈ 0.0005

The argument fails because the conjunction of premises is improbable.

Source: Edgington (1997)
-/
def tallProbabilisticSorites : ProbabilisticSoritesData :=
  { predicate := "tall"
  , singleStepProbability := 0.99
  , numSteps := 762
  , cumulativeProbability := 0.0005  -- 0.99^762
  , premise1Accepted := true
  , eachStepAccepted := true
  , fullArgumentAccepted := false  -- conjunction fails!
  }

def probabilisticSoritesExamples : List ProbabilisticSoritesData :=
  [tallProbabilisticSorites]

-- ============================================================================
-- PART 10: Theoretical Positions (Theory-Neutral Characterization)
-- ============================================================================

/--
Major theoretical positions on vagueness.

This is a theory-neutral characterization of what each position claims.
The phenomena above serve as test cases for these positions.

Source: Keefe (2000), Williamson (1994)
-/
inductive VaguenessTheoryType where
  | epistemicism       -- Sharp boundaries exist but are unknowable
  | supervaluationism  -- Truth = truth on all precisifications
  | degreeTheory       -- Truth comes in degrees (fuzzy logic)
  | contextualism      -- Vagueness = context-sensitivity
  | nihilism           -- Vague predicates have no extension
  deriving Repr, DecidableEq

/--
Data characterizing what each theory says about key phenomena.

This allows us to track which theories predict which patterns.

Source: Keefe (2000)
-/
structure TheoryPredictionProfile where
  /-- The theory -/
  theory : VaguenessTheoryType
  /-- Does theory posit sharp boundaries? -/
  hasSharpBoundaries : Bool
  /-- Does theory preserve classical logic (LEM, non-contradiction)? -/
  preservesClassicalLogic : Bool
  /-- Does theory allow truth value gaps? -/
  allowsTruthValueGaps : Bool
  /-- Does theory allow degrees of truth? -/
  allowsDegreesOfTruth : Bool
  /-- How does theory handle sorites? -/
  soritesResolution : String
  /-- How does theory handle higher-order vagueness? -/
  higherOrderResponse : String
  deriving Repr

def epistemicismProfile : TheoryPredictionProfile :=
  { theory := .epistemicism
  , hasSharpBoundaries := true
  , preservesClassicalLogic := true
  , allowsTruthValueGaps := false
  , allowsDegreesOfTruth := false
  , soritesResolution := "One premise is false; we just don't know which"
  , higherOrderResponse := "Sharp boundary exists; we don't know where"
  }

def supervaluationismProfile : TheoryPredictionProfile :=
  { theory := .supervaluationism
  , hasSharpBoundaries := false  -- no single boundary
  , preservesClassicalLogic := true  -- globally
  , allowsTruthValueGaps := true  -- borderline cases
  , allowsDegreesOfTruth := false
  , soritesResolution := "Induction premise is super-false (false on some precisification)"
  , higherOrderResponse := "Problematic - precisifications may themselves be vague"
  }

def degreeTheoryProfile : TheoryPredictionProfile :=
  { theory := .degreeTheory
  , hasSharpBoundaries := false
  , preservesClassicalLogic := false  -- LEM fails locally
  , allowsTruthValueGaps := false
  , allowsDegreesOfTruth := true
  , soritesResolution := "Each step slightly lowers truth value; cumulative effect is large"
  , higherOrderResponse := "Can iterate degrees: degree of being degree 0.5 tall"
  }

def contextualismProfile : TheoryPredictionProfile :=
  { theory := .contextualism
  , hasSharpBoundaries := true  -- in each context
  , preservesClassicalLogic := true
  , allowsTruthValueGaps := false
  , allowsDegreesOfTruth := false
  , soritesResolution := "Context shifts mid-argument, making it equivocal"
  , higherOrderResponse := "Higher-order vagueness = higher-order context-sensitivity"
  }

def theoryProfiles : List TheoryPredictionProfile :=
  [epistemicismProfile, supervaluationismProfile, degreeTheoryProfile, contextualismProfile]

-- ============================================================================
-- PART 11: Formal Constraints Any Theory Must Satisfy
-- ============================================================================

/--
Formal constraints that any adequate theory of vagueness should satisfy.

These are theory-neutral desiderata. A theory's success is measured
by how well it accounts for these patterns.

Source: Various (Keefe 2000, Williamson 1994, Lassiter 2017)
-/
structure VaguenessDesideratum where
  /-- Name of the constraint -/
  name : String
  /-- Informal description -/
  description : String
  /-- Formal statement (in natural language) -/
  formalStatement : String
  /-- Why this matters -/
  importance : String
  deriving Repr

def borderlineCasesExist : VaguenessDesideratum :=
  { name := "Borderline Cases"
  , description := "Vague predicates have cases where judgment is uncertain"
  , formalStatement := "∃x. ¬Determinately(P(x)) ∧ ¬Determinately(¬P(x))"
  , importance := "Distinguishes vagueness from mere ignorance"
  }

def toleranceIntuition : VaguenessDesideratum :=
  { name := "Tolerance"
  , description := "Tiny differences can't matter for vague predicates"
  , formalStatement := "∀x y. |x - y| < ε → (P(x) → P(y))"
  , importance := "Captures the phenomenology of vagueness"
  }

def soritesParadoxicality : VaguenessDesideratum :=
  { name := "Sorites Paradoxicality"
  , description := "The sorites is genuinely paradoxical, not just a fallacy"
  , formalStatement := "Premises seem true, argument seems valid, conclusion seems false"
  , importance := "Any resolution must explain why the argument seems compelling"
  }

def penumbralPreservation : VaguenessDesideratum :=
  { name := "Penumbral Preservation"
  , description := "Classical logic holds even in borderline cases"
  , formalStatement := "P ∨ ¬P is true even when P is borderline"
  , importance := "Distinguishes vagueness from ambiguity"
  }

def contextSensitivity : VaguenessDesideratum :=
  { name := "Context Sensitivity"
  , description := "Thresholds vary with comparison class (for RGAs)"
  , formalStatement := "Tall-for-class-C₁ ≠ Tall-for-class-C₂"
  , importance := "Captures the flexibility of natural language"
  }

def higherOrderProblem : VaguenessDesideratum :=
  { name := "Higher-Order Vagueness"
  , description := "The boundary of borderline cases is itself vague"
  , formalStatement := "∃x. ¬Det(Borderline(P, x)) ∧ ¬Det(¬Borderline(P, x))"
  , importance := "Sharp boundaries for borderline ≈ sharp boundaries for P"
  }

def desiderata : List VaguenessDesideratum :=
  [borderlineCasesExist, toleranceIntuition, soritesParadoxicality,
   penumbralPreservation, contextSensitivity, higherOrderProblem]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types

**Empirical Patterns**
- `ContextShiftDatum`: Context-sensitivity of thresholds
- `BorderlineDatum`: Borderline case patterns
- `SoritesDatum`: Sorites paradox patterns
- `AntonymDatum`: Antonym pair behavior

**Kennedy (2007) Typology**
- `AdjectiveClass`: RGA vs AGA-max vs AGA-min classification
- `AdjectiveTypologyDatum`: Typology data with diagnostics
- `RGAvsAGAPrediction`: Context-sensitivity prediction

**Degree Modifiers**
- `DegreeModifierType`: Proportional, measure phrase, intensifier, diminisher
- `DegreeModifierDatum`: Modifier compatibility patterns
- `ScaleClosurePuzzle`: Why "completely tall" is odd

**Higher-Order Vagueness**
- `HigherOrderVaguenessData`: Borderline of borderline problem
- `DefinitelyOperatorData`: "Definitely" operator and iteration

**Penumbral Connections**
- `PenumbralConnectionData`: Classical logic in borderline region

**Sorites and Tolerance**
- `TolerancePrincipleData`: The key sorites ingredient
- `ProbabilisticSoritesData`: Edgington's probabilistic dissolution

**Theoretical Landscape**
- `VaguenessTheoryType`: Epistemicism, supervaluationism, etc.
- `TheoryPredictionProfile`: What each theory predicts
- `VaguenessDesideratum`: Theory-neutral constraints

### Example Collections
- `contextShiftExamples`: 3 examples (jockey/basketball, Atlanta/SF, microbe/planet)
- `borderlineExamples`: 2 examples (expensive house, tall person)
- `soritesExamples`: 3 examples (tall, heap, expensive)
- `antonymExamples`: 2 examples (tall/short, expensive/cheap)
- `adjectiveTypologyExamples`: 5 examples (tall, full, wet, straight, bent)
- `degreeModifierExamples`: 4 examples (completely, slightly, very, half)
- `higherOrderExamples`: 1 example (tall higher-order)
- `penumbralExamples`: 4 examples (LEM, non-contradiction, same-height, comparative)
- `toleranceExamples`: 2 examples (height, price)
- `probabilisticSoritesExamples`: 1 example (tall)
- `theoryProfiles`: 4 theories characterized
- `desiderata`: 6 constraints any theory should satisfy

### Key References
- Fine (1975): Vagueness, truth and logic (supervaluationism, penumbral connections)
- Kamp (1975): Two theories about adjectives
- Wright (1976): Tolerance and sorites
- Klein (1980): Comparison class approach
- Williamson (1994): Vagueness (epistemicism, higher-order vagueness)
- Edgington (1997): Vagueness by degrees (probabilistic sorites)
- Fara (2000): Interest-relative theory
- Keefe (2000): Theories of vagueness
- Kennedy (2007): Vagueness and grammar (adjective typology)
- Burnett (2017): Gradability in Natural Language
- Lassiter & Goodman (2017): Adjectival vagueness in a Bayesian model

### Formal Targets

The desiderata define what an adequate theory must explain:
1. Borderline cases exist and are distinct from ignorance
2. Tolerance intuition is compelling (tiny differences don't matter)
3. Sorites is genuinely paradoxical (not just a fallacy)
4. Penumbral connections hold (classical logic preserved)
5. Context-sensitivity for RGAs (thresholds shift)
6. Higher-order vagueness threatens sharp boundaries everywhere

These serve as formal targets for theories in `Theories/RSA/` and beyond.
-/

end Phenomena.Vagueness
