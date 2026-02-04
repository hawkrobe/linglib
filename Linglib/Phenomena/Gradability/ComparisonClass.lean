/-
# Comparison Class: Empirical Data

Theory-neutral empirical patterns for comparison class inference with
gradable adjectives.

## Phenomena Covered

1. **Polarity × Expectations Interaction**: Adjective polarity interacts with
   prior expectations to determine inferred comparison class
2. **Linguistic vs Visual Cues**: Taxonomic labels dominate visual context
3. **RGA vs AGA Distinction**: Relative vs absolute gradable adjectives differ
   in comparison class sensitivity

## Key References

- Tessler, M. H. & Goodman, N. D. (2019). The Language of Generalization. Psych Review.
- Tessler, M. H. & Goodman, N. D. (2022). "Warm (for Winter)": Comparison Class
  Understanding Is an Embedded Probabilistic Inference.
- Weicker, L. & Schulz, P. (2024). Linguistic versus visual information in comparison
  class determination: Children's and adults' interpretation of gradable adjectives.
  Glossa: a journal of general linguistics 9(1).
-/

namespace Phenomena.Gradability.ComparisonClass


/--
Empirical pattern: Polarity and prior expectations interact to determine
the inferred comparison class.

Key prediction:
- Positive adjective + expected property → superordinate class
  (e.g., "tall basketball player" → compared to people in general)
- Negative adjective + expected property → subordinate class
  (e.g., "short basketball player" → compared to basketball players)
- The pattern reverses when expectations reverse
  (e.g., "short jockey" → compared to people; "tall jockey" → compared to jockeys)

Source: Tessler & Goodman (2022), Section 3
-/
structure PolarityExpectationsDatum where
  /-- The adjective used -/
  adjective : String
  /-- Polarity of the adjective (positive or negative) -/
  polarity : String  -- "positive" or "negative"
  /-- The noun/kind mentioned -/
  noun : String
  /-- Prior expectation direction for this kind ("high" or "low") -/
  priorExpectation : String
  /-- Inferred comparison class -/
  inferredClass : String  -- "subordinate" or "superordinate"
  deriving Repr

/--
"Tall basketball player" → compared to people in general (superordinate).

When you hear someone is a "tall basketball player", the most informative
interpretation is that they are tall even compared to people in general,
since basketball players are expected to be tall anyway.

Source: Tessler & Goodman (2022) Section 3.1
-/
def tallBasketball : PolarityExpectationsDatum :=
  { adjective := "tall"
  , polarity := "positive"
  , noun := "basketball player"
  , priorExpectation := "high"  -- basketball players expected tall
  , inferredClass := "superordinate"  -- compared to people
  }

/--
"Short basketball player" → compared to basketball players (subordinate).

The negative adjective with high prior expectation leads to subordinate
comparison: "short for a basketball player".

Source: Tessler & Goodman (2022) Section 3.1
-/
def shortBasketball : PolarityExpectationsDatum :=
  { adjective := "short"
  , polarity := "negative"
  , noun := "basketball player"
  , priorExpectation := "high"
  , inferredClass := "subordinate"
  }

/--
"Short jockey" → compared to people in general (superordinate).

The pattern reverses for jockeys: negative adjective + low prior → superordinate.
"Short for a person" is more informative than "short for a jockey".

Source: Tessler & Goodman (2022) Section 3.1
-/
def shortJockey : PolarityExpectationsDatum :=
  { adjective := "short"
  , polarity := "negative"
  , noun := "jockey"
  , priorExpectation := "low"  -- jockeys expected short
  , inferredClass := "superordinate"
  }

/--
"Tall jockey" → compared to jockeys (subordinate).

Positive adjective + low prior → subordinate comparison class.

Source: Tessler & Goodman (2022) Section 3.1
-/
def tallJockey : PolarityExpectationsDatum :=
  { adjective := "tall"
  , polarity := "positive"
  , noun := "jockey"
  , priorExpectation := "low"
  , inferredClass := "subordinate"
  }

/--
All polarity × expectations examples.
-/
def polarityExpectationsExamples : List PolarityExpectationsDatum :=
  [tallBasketball, shortBasketball, shortJockey, tallJockey]

/--
The polarity × expectations interaction pattern.

This captures the core empirical generalization:
- positive adjective + high prior → superordinate
- negative adjective + high prior → subordinate
- positive adjective + low prior → subordinate
- negative adjective + low prior → superordinate

Source: Tessler & Goodman (2022) Table 1
-/
structure PolarityExpectationsPattern where
  /-- Examples demonstrating the pattern -/
  examples : List PolarityExpectationsDatum
  /-- Does pattern show expected-leads-to-superordinate for positive adjectives? -/
  positivePlusHighYieldsSuperordinate : Bool
  /-- Does pattern show expected-leads-to-subordinate for negative adjectives? -/
  negativePlusHighYieldsSubordinate : Bool
  deriving Repr

def tesslerGoodmanPattern : PolarityExpectationsPattern :=
  { examples := polarityExpectationsExamples
  , positivePlusHighYieldsSuperordinate := true
  , negativePlusHighYieldsSubordinate := true
  }


/--
Adjective type: Relative Gradable (RGA) vs Absolute Gradable (AGA).

- RGA: Requires comparison class for interpretation (big, tall, expensive)
- AGA: Has inherent standard, less dependent on comparison class (wet, closed, full)

Source: Weicker & Schulz (2024), Section 1.2
-/
inductive AdjectiveType where
  | RGA  -- Relative Gradable Adjective
  | AGA  -- Absolute Gradable Adjective
  deriving Repr, DecidableEq

/--
Structure capturing the difference in comparison class dependency between
RGA and AGA adjectives.

Source: Weicker & Schulz (2024), Section 1.2
-/
structure AdjectiveTypeDatum where
  /-- The adjective -/
  adjective : String
  /-- Adjective type -/
  adjType : AdjectiveType
  /-- Example showing context-sensitivity (or lack thereof) -/
  example1 : String
  /-- Another example -/
  example2 : String
  /-- Does threshold shift with comparison class? -/
  thresholdShifts : Bool
  deriving Repr

/--
"Big" is an RGA - threshold shifts with comparison class.

Source: Weicker & Schulz (2024), citing Kennedy (2007)
-/
def bigRGA : AdjectiveTypeDatum :=
  { adjective := "big"
  , adjType := .RGA
  , example1 := "The mouse is big [for a mouse]"
  , example2 := "The elephant is big [for an elephant]"
  , thresholdShifts := true
  }

/--
"Wet" is an AGA - has inherent minimum standard.

Source: Weicker & Schulz (2024), Section 1.2
-/
def wetAGA : AdjectiveTypeDatum :=
  { adjective := "wet"
  , adjType := .AGA
  , example1 := "The towel is wet (any amount of wetness)"
  , example2 := "Not relative to a comparison class"
  , thresholdShifts := false
  }

def adjectiveTypeExamples : List AdjectiveTypeDatum :=
  [bigRGA, wetAGA]


/--
Cue type for comparison class determination.

Source: Weicker & Schulz (2024), Section 1.3
-/
inductive CueType where
  | linguistic  -- Taxonomic label (e.g., "the tall animal")
  | visual      -- Visual context (e.g., shown mice vs elephants)
  deriving Repr, DecidableEq

/--
Noun level in taxonomic hierarchy.

Source: Weicker & Schulz (2024), Section 2
-/
inductive NounLevel where
  | basic        -- "dog", "mouse", "elephant"
  | superordinate -- "animal", "mammal"
  deriving Repr, DecidableEq

/--
Empirical pattern: Linguistic cues dominate visual cues for comparison class.

Key finding: When taxonomic label conflicts with visual context, both children
and adults privilege the linguistic information.

- "The big animal" + visual context of mice → compare to animals (linguistic wins)
- Basic-level nouns trigger subordinate class, superordinate nouns trigger
  superordinate class

Source: Weicker & Schulz (2024), Section 4
-/
structure LinguisticVsVisualDatum where
  /-- The adjective used -/
  adjective : String
  /-- The noun used (determines linguistic cue) -/
  noun : String
  /-- Level of the noun -/
  nounLevel : NounLevel
  /-- Visual context description -/
  visualContext : String
  /-- What comparison class is inferred? -/
  inferredClass : String
  /-- Which cue dominates? -/
  dominantCue : CueType
  deriving Repr

/--
"The big animal" with mice visible → animal comparison class.

The superordinate noun "animal" triggers the superordinate comparison class,
overriding the visual context of only mice being present.

Source: Weicker & Schulz (2024), Experiment 1
-/
def bigAnimalMice : LinguisticVsVisualDatum :=
  { adjective := "big"
  , noun := "animal"
  , nounLevel := .superordinate
  , visualContext := "Only mice visible"
  , inferredClass := "animals (superordinate)"
  , dominantCue := .linguistic
  }

/--
"The big mouse" with various animals visible → mouse comparison class.

The basic-level noun "mouse" triggers the subordinate comparison class
(compared to mice), even when other animals are visually salient.

Source: Weicker & Schulz (2024), Experiment 1
-/
def bigMouseAnimals : LinguisticVsVisualDatum :=
  { adjective := "big"
  , noun := "mouse"
  , nounLevel := .basic
  , visualContext := "Various animals visible"
  , inferredClass := "mice (subordinate)"
  , dominantCue := .linguistic
  }

def linguisticVsVisualExamples : List LinguisticVsVisualDatum :=
  [bigAnimalMice, bigMouseAnimals]


/--
Empirical pattern: Children show same linguistic > visual preference as adults.

Key finding: Both 4-6 year olds and adults privilege linguistic over visual
information, though adults show larger subordinate selections with basic-level
nouns (possible scalar implicature contribution).

Source: Weicker & Schulz (2024), Section 4
-/
structure DevelopmentalDatum where
  /-- Age group -/
  ageGroup : String
  /-- Condition (noun level) -/
  nounLevel : NounLevel
  /-- Proportion selecting subordinate interpretation -/
  subordinateSelection : Float
  /-- Proportion selecting superordinate interpretation -/
  superordinateSelection : Float
  deriving Repr

/--
Adults with basic-level nouns strongly prefer subordinate interpretation.

Source: Weicker & Schulz (2024), Figure 2
-/
def adultBasicLevel : DevelopmentalDatum :=
  { ageGroup := "Adults"
  , nounLevel := .basic
  , subordinateSelection := 0.86  -- approximately 86%
  , superordinateSelection := 0.14
  }

/--
Adults with superordinate nouns prefer superordinate interpretation.

Source: Weicker & Schulz (2024), Figure 2
-/
def adultSuperordinate : DevelopmentalDatum :=
  { ageGroup := "Adults"
  , nounLevel := .superordinate
  , subordinateSelection := 0.40  -- approximately 40%
  , superordinateSelection := 0.60
  }

/--
Children with basic-level nouns prefer subordinate interpretation.

Source: Weicker & Schulz (2024), Figure 2
-/
def childBasicLevel : DevelopmentalDatum :=
  { ageGroup := "4-6 year olds"
  , nounLevel := .basic
  , subordinateSelection := 0.68  -- approximately 68%
  , superordinateSelection := 0.32
  }

/--
Children with superordinate nouns prefer superordinate interpretation.

Source: Weicker & Schulz (2024), Figure 2
-/
def childSuperordinate : DevelopmentalDatum :=
  { ageGroup := "4-6 year olds"
  , nounLevel := .superordinate
  , subordinateSelection := 0.38  -- approximately 38%
  , superordinateSelection := 0.62
  }

def developmentalExamples : List DevelopmentalDatum :=
  [adultBasicLevel, adultSuperordinate, childBasicLevel, childSuperordinate]


/--
Main empirical generalizations about comparison class inference.

Source: Tessler & Goodman (2022), Weicker & Schulz (2024)
-/
structure ComparisonClassGeneralizations where
  /-- Polarity interacts with prior expectations -/
  polarityExpectationsInteraction : Bool
  /-- Linguistic cues dominate visual cues -/
  linguisticDominatesVisual : Bool
  /-- Basic-level nouns trigger subordinate classes -/
  basicLevelYieldsSubordinate : Bool
  /-- Superordinate nouns trigger superordinate classes -/
  superordinateYieldsSuperordinate : Bool
  /-- Pattern holds across development (adults and children) -/
  developmentallyStable : Bool
  /-- RGAs more context-sensitive than AGAs -/
  rgaMoreContextSensitive : Bool
  deriving Repr

def mainGeneralizations : ComparisonClassGeneralizations :=
  { polarityExpectationsInteraction := true
  , linguisticDominatesVisual := true
  , basicLevelYieldsSubordinate := true
  , superordinateYieldsSuperordinate := true
  , developmentallyStable := true
  , rgaMoreContextSensitive := true
  }

-- Summary

/-
## What This Module Provides

### Data Types
- `PolarityExpectationsDatum`: Polarity × expectations interaction
- `PolarityExpectationsPattern`: The systematic pattern
- `AdjectiveTypeDatum`: RGA vs AGA distinction
- `LinguisticVsVisualDatum`: Cue competition patterns
- `DevelopmentalDatum`: Age-related patterns
- `ComparisonClassGeneralizations`: Key empirical generalizations

### Example Collections
- `polarityExpectationsExamples`: 4 examples (tall/short × basketball/jockey)
- `adjectiveTypeExamples`: 2 examples (big RGA, wet AGA)
- `linguisticVsVisualExamples`: 2 examples (linguistic dominance)
- `developmentalExamples`: 4 examples (adults/children × basic/superordinate)

### Key References
- Tessler & Goodman (2022): Comparison class as embedded inference
- Weicker & Schulz (2024): Linguistic vs visual cues across development
- Kennedy (2007): Vagueness and grammar
- Syrett et al. (2010): Prior work on RGA/AGA acquisition
-/

end Phenomena.Gradability.ComparisonClass
