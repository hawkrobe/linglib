/-
# Homogeneity: Empirical Data

Theory-neutral empirical patterns for homogeneity gaps in natural language.

## Phenomena Covered

1. **Plural definites**: "The doors are open" / "The doors aren't open"
2. **Conjunctions**: "Ann and Bert have red hair"
3. **Summative predicates**: "The flag is blue"
4. **Conditionals**: "They play if the sun shines"
5. **Collective predicates**: "The teachers met"

## Key Observation

Homogeneity is characterized by non-complementary truth conditions:
- Positive: requires universal (or near-universal) satisfaction
- Negative: requires existential denial (none satisfy)
- Gap: some but not all satisfy → neither clearly true nor false

## Key References

- Löbner (2000): Polarity in natural language
- Križ (2015, 2016): Homogeneity, trivalence, non-maximality
- Križ & Chemla (2015): Experimental investigation
- Križ & Spector (2021): Supervaluationist approach
- Bar-Lev (2021a): Exhaustification approach
-/

namespace Phenomena.Imprecision.Homogeneity

-- ============================================================================
-- PART 1: Basic Homogeneity Pattern
-- ============================================================================

/--
Polarity of a sentence (for homogeneity asymmetry).
-/
inductive Polarity where
  | positive
  | negative
  deriving Repr, DecidableEq

/--
Judgment type for homogeneity scenarios.
-/
inductive HomogeneityJudgment where
  | clearlyTrue
  | clearlyFalse
  | neitherTrueNorFalse  -- the gap
  | marginal
  deriving Repr, DecidableEq

/--
Basic homogeneity datum: a sentence pair showing the gap.
-/
structure HomogeneityDatum where
  /-- The positive sentence -/
  positiveSentence : String
  /-- The negative sentence -/
  negativeSentence : String
  /-- Description of the "all" scenario -/
  allScenario : String
  /-- Description of the "none" scenario -/
  noneScenario : String
  /-- Description of the "some but not all" scenario -/
  gapScenario : String
  /-- Judgment in all scenario -/
  positiveInAll : HomogeneityJudgment
  negativeInAll : HomogeneityJudgment
  /-- Judgment in none scenario -/
  positiveInNone : HomogeneityJudgment
  negativeInNone : HomogeneityJudgment
  /-- Judgment in gap scenario -/
  positiveInGap : HomogeneityJudgment
  negativeInGap : HomogeneityJudgment
  deriving Repr

-- ============================================================================
-- PART 2: Plural Definites
-- ============================================================================

/--
The canonical example: "The switches are on."

In a scenario with 10 switches:
- All on: positive true, negative false
- None on: positive false, negative true
- 5 on: neither clearly true nor false

Source: Križ (2015), Križ & Chemla (2015)
-/
def switchesExample : HomogeneityDatum :=
  { positiveSentence := "The switches are on."
  , negativeSentence := "The switches are not on." -- or: "It's not the case that the switches are on."
  , allScenario := "All 10 switches are on"
  , noneScenario := "None of the 10 switches are on"
  , gapScenario := "5 of the 10 switches are on"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  , positiveInGap := .neitherTrueNorFalse
  , negativeInGap := .neitherTrueNorFalse
  }

/--
Books example from Križ & Chemla (2015) experimental design.

Source: Križ & Chemla (2015)
-/
def booksExample : HomogeneityDatum :=
  { positiveSentence := "Ann liked the books."
  , negativeSentence := "Ann didn't like the books."
  , allScenario := "Ann liked all 6 shortlisted books"
  , noneScenario := "Ann liked none of the 6 shortlisted books"
  , gapScenario := "Ann liked 3 of the 6 shortlisted books"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  , positiveInGap := .neitherTrueNorFalse
  , negativeInGap := .neitherTrueNorFalse
  }

-- ============================================================================
-- PART 3: Conjunctions
-- ============================================================================

/--
Conjunctions exhibit homogeneity but resist non-maximal readings.

Key observation: "Ann and Bert have red hair" behaves like a plural definite
for homogeneity, but unlike plural definites, it resists non-maximal readings.

Source: Schwarzschild (1994), Križ (2015), dissertation Chapter 7
-/
def conjunctionExample : HomogeneityDatum :=
  { positiveSentence := "Ann and Bert have red hair."
  , negativeSentence := "Ann and Bert don't have red hair."
  , allScenario := "Both Ann and Bert have red hair"
  , noneScenario := "Neither Ann nor Bert has red hair"
  , gapScenario := "Ann has red hair but Bert doesn't"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  , positiveInGap := .neitherTrueNorFalse
  , negativeInGap := .neitherTrueNorFalse
  }

/--
The contrast between conjunctions and plural definites for non-maximality.

Source: Brisson (1998), Križ (2015), dissertation (18)
-/
structure ConjunctionVsPluralDatum where
  /-- The conjunction sentence -/
  conjunctionSentence : String
  /-- The plural definite sentence -/
  pluralSentence : String
  /-- Context description -/
  context : String
  /-- Does the conjunction permit non-maximal reading? -/
  conjunctionPermitsNonMax : Bool
  /-- Does the plural permit non-maximal reading? -/
  pluralPermitsNonMax : Bool
  deriving Repr

def coworkersExample : ConjunctionVsPluralDatum :=
  { conjunctionSentence := "Bert, Claire and Dora went there."
  , pluralSentence := "My coworkers went there."
  , context := "Dean hosted a party. Ann has three coworkers. She vaguely remembers that two of them went."
  , conjunctionPermitsNonMax := false  -- marginal/unacceptable
  , pluralPermitsNonMax := true        -- acceptable
  }

-- ============================================================================
-- PART 4: Summative Predicates
-- ============================================================================

/--
Summative predicates: apply to parts of a singular entity.

"The flag is blue" requires all (salient) parts to be blue.

Source: Löbner (2000), Križ (2015), Amiraz (2020), Paillé (2020, 2022)
-/
def summativeExample : HomogeneityDatum :=
  { positiveSentence := "The flag is blue."
  , negativeSentence := "The flag is not blue."
  , allScenario := "The entire flag is blue"
  , noneScenario := "No part of the flag is blue"
  , gapScenario := "Half the flag is blue, half is white"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  , positiveInGap := .neitherTrueNorFalse
  , negativeInGap := .neitherTrueNorFalse
  }

-- ============================================================================
-- PART 5: Conditionals
-- ============================================================================

/--
Bare conditionals exhibit homogeneity over situations.

Source: von Fintel (1997), Gajewski (2005), Križ (2015)
-/
def conditionalExample : HomogeneityDatum :=
  { positiveSentence := "They play soccer if the sun shines."
  , negativeSentence := "I don't think they play soccer if the sun shines."
  , allScenario := "In all relevant sunny situations, they play soccer"
  , noneScenario := "In no relevant sunny situations do they play soccer"
  , gapScenario := "In some but not all sunny situations, they play soccer"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  , positiveInGap := .neitherTrueNorFalse
  , negativeInGap := .neitherTrueNorFalse
  }

-- ============================================================================
-- PART 6: Collective Predicates
-- ============================================================================

/--
Collective predicates: "The teachers met."

Homogeneity concerns whether ALL teachers participated in a meeting,
or just some subgroup.

Source: Križ (2015, 2019)
-/
def collectiveExample : HomogeneityDatum :=
  { positiveSentence := "The teachers met last week."
  , negativeSentence := "The teachers didn't meet last week."
  , allScenario := "All teachers participated in a meeting"
  , noneScenario := "No subgroup of teachers met"
  , gapScenario := "Some teachers met, but not all participated"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  , positiveInGap := .neitherTrueNorFalse
  , negativeInGap := .neitherTrueNorFalse
  }

/--
"Upward homogeneity" in collective predication.

When a plurality is part of a larger group that satisfies a collective predicate,
the smaller plurality is neither clearly a satisfier nor clearly not.

Source: Križ (2015, 2019), Chatain (2021)
-/
structure UpwardHomogeneityDatum where
  /-- The sentence -/
  sentence : String
  /-- Scenario description -/
  scenario : String
  /-- Judgment -/
  judgment : HomogeneityJudgment
  deriving Repr

def hamletExample : UpwardHomogeneityDatum :=
  { sentence := "The boys are performing Hamlet."
  , scenario := "All students (boys and girls together) are performing Hamlet."
  , judgment := .neitherTrueNorFalse
  }

-- ============================================================================
-- PART 7: Homogeneity Removal
-- ============================================================================

/--
Elements that remove homogeneity gaps.
-/
inductive HomogeneityRemover where
  | all           -- "all the doors"
  | both          -- "both Ann and Bert"
  | every         -- "every door"
  | each          -- "each door"
  | completely    -- "completely blue"
  deriving Repr, DecidableEq

/--
Datum showing homogeneity removal.
-/
structure HomogeneityRemovalDatum where
  /-- Sentence with homogeneity -/
  homogeneousSentence : String
  /-- Sentence with homogeneity removed -/
  precisesentence : String
  /-- What removes homogeneity -/
  remover : HomogeneityRemover
  /-- Gap scenario -/
  gapScenario : String
  /-- Judgment for homogeneous sentence in gap -/
  homogeneousJudgment : HomogeneityJudgment
  /-- Judgment for precise sentence in gap -/
  preciseJudgment : HomogeneityJudgment
  deriving Repr

def allRemovesHomogeneity : HomogeneityRemovalDatum :=
  { homogeneousSentence := "The doors are open."
  , precisesentence := "All the doors are open."
  , remover := .all
  , gapScenario := "8 of 10 doors are open"
  , homogeneousJudgment := .neitherTrueNorFalse
  , preciseJudgment := .clearlyFalse
  }

def bothRemovesHomogeneity : HomogeneityRemovalDatum :=
  { homogeneousSentence := "Ann and Bert have red hair."
  , precisesentence := "Both Ann and Bert have red hair."
  , remover := .both
  , gapScenario := "Ann has red hair, Bert doesn't"
  , homogeneousJudgment := .neitherTrueNorFalse
  , preciseJudgment := .clearlyFalse
  }

def completelyRemovesHomogeneity : HomogeneityRemovalDatum :=
  { homogeneousSentence := "The flag is blue."
  , precisesentence := "The flag is completely blue."
  , remover := .completely
  , gapScenario := "Half the flag is blue"
  , homogeneousJudgment := .neitherTrueNorFalse
  , preciseJudgment := .clearlyFalse
  }

-- ============================================================================
-- PART 8: Question-Answer Diagnostic
-- ============================================================================

/--
Responses to questions in gap scenarios.

Neither "yes" nor "no" is fully appropriate.

Source: Križ (2015)
-/
structure QuestionAnswerDatum where
  /-- The question -/
  question : String
  /-- Gap scenario -/
  scenario : String
  /-- Is "Yes" appropriate? -/
  yesAppropriate : Bool
  /-- Is "No" appropriate? -/
  noAppropriate : Bool
  /-- Better response -/
  betterResponse : String
  deriving Repr

def booksQuestionExample : QuestionAnswerDatum :=
  { question := "Did you like the books?"
  , scenario := "Ann read 6 books, liked 3, disliked 3"
  , yesAppropriate := false
  , noAppropriate := false
  , betterResponse := "Well, I liked some of them..."
  }

-- ============================================================================
-- PART 9: Key Generalizations
-- ============================================================================

/--
Core empirical generalizations about homogeneity.
-/
structure HomogeneityGeneralizations where
  /-- Positive sentences get universal-like truth conditions -/
  positiveUniversal : Bool
  /-- Negative sentences get existential-like falsity conditions -/
  negativeExistential : Bool
  /-- Gap scenarios yield neither-true-nor-false judgments -/
  gapYieldsNeither : Bool
  /-- All/both/every remove the gap -/
  quantifiersRemoveGap : Bool
  /-- Conjunctions have gaps but resist non-maximality -/
  conjunctionsResistNonMax : Bool
  deriving Repr

def mainGeneralizations : HomogeneityGeneralizations :=
  { positiveUniversal := true
  , negativeExistential := true
  , gapYieldsNeither := true
  , quantifiersRemoveGap := true
  , conjunctionsResistNonMax := true
  }

-- ============================================================================
-- Collections
-- ============================================================================

def pluralDefiniteExamples : List HomogeneityDatum :=
  [switchesExample, booksExample]

def otherHomogeneityExamples : List HomogeneityDatum :=
  [conjunctionExample, summativeExample, conditionalExample, collectiveExample]

def removalExamples : List HomogeneityRemovalDatum :=
  [allRemovesHomogeneity, bothRemovesHomogeneity, completelyRemovesHomogeneity]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `HomogeneityDatum`: Basic pattern (positive/negative/gap scenarios)
- `ConjunctionVsPluralDatum`: Contrast for non-maximality
- `UpwardHomogeneityDatum`: Collective predicate patterns
- `HomogeneityRemovalDatum`: How elements remove gaps
- `QuestionAnswerDatum`: Question-response patterns

### Example Collections
- `pluralDefiniteExamples`: switches, books
- `otherHomogeneityExamples`: conjunctions, summatives, conditionals, collectives
- `removalExamples`: all, both, completely

### Key References
- Löbner (2000), Križ (2015, 2016), Križ & Chemla (2015)
- Križ & Spector (2021), Bar-Lev (2021a)
-/

end Phenomena.Imprecision.Homogeneity
