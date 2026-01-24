/-
# Disjunction Ignorance: Empirical Data

Theory-neutral empirical patterns for ignorance inferences from disjunction.

## The Pattern

"Harry is in Antwerp or Brussels" implicates:
1. Speaker doesn't know Harry is in Antwerp
2. Speaker doesn't know Harry is in Brussels

This is different from scalar implicature:
- Scalar: "some" → speaker KNOWS not all
- Ignorance: "A or B" → speaker DOESN'T KNOW which

## Key References

- Gazdar, G. (1979). Pragmatics: Implicature, Presupposition, and Logical Form.
- Sauerland, U. (2004). Scalar Implicatures in Complex Sentences.
- Geurts, B. (2010). Quantity Implicatures. Ch. 3.3.
-/

namespace Phenomena.DisjunctionIgnorance

-- ============================================================================
-- PART 1: Basic Ignorance Data
-- ============================================================================

/--
Empirical pattern: Disjunction and speaker ignorance.

"Harry is in Antwerp or Brussels" implicates:
1. Speaker doesn't know Harry is in Antwerp
2. Speaker doesn't know Harry is in Brussels

Source: Gazdar (1979), Geurts (2010) Ch. 3.3
-/
structure DisjunctionIgnoranceDatum where
  /-- The disjunctive statement -/
  disjunction : String
  /-- First disjunct -/
  disjunctA : String
  /-- Second disjunct -/
  disjunctB : String
  /-- Ignorance inference about A -/
  inferenceA : String
  /-- Ignorance inference about B -/
  inferenceB : String
  deriving Repr

/--
Classic example: Harry's location.
Source: Geurts (2010) p.61
-/
def harryLocation : DisjunctionIgnoranceDatum :=
  { disjunction := "Harry is in Antwerp or Brussels"
  , disjunctA := "Harry is in Antwerp"
  , disjunctB := "Harry is in Brussels"
  , inferenceA := "Speaker doesn't know Harry is in Antwerp"
  , inferenceB := "Speaker doesn't know Harry is in Brussels"
  }

/--
Location example with Mary.
-/
def maryLocation : DisjunctionIgnoranceDatum :=
  { disjunction := "Mary went to Paris or London"
  , disjunctA := "Mary went to Paris"
  , disjunctB := "Mary went to London"
  , inferenceA := "Speaker doesn't know Mary went to Paris"
  , inferenceB := "Speaker doesn't know Mary went to London"
  }

/--
Activity example.
-/
def johnActivity : DisjunctionIgnoranceDatum :=
  { disjunction := "John is reading or sleeping"
  , disjunctA := "John is reading"
  , disjunctB := "John is sleeping"
  , inferenceA := "Speaker doesn't know John is reading"
  , inferenceB := "Speaker doesn't know John is sleeping"
  }

/--
All basic ignorance examples.
-/
def disjunctionIgnoranceExamples : List DisjunctionIgnoranceDatum :=
  [harryLocation, maryLocation, johnActivity]

-- ============================================================================
-- PART 2: Ignorance vs Scalar Implicature
-- ============================================================================

/--
Comparison between ignorance and scalar implicatures.

Key difference:
- Scalar: Speaker KNOWS the stronger alternative is false
- Ignorance: Speaker DOESN'T KNOW which disjunct is true
-/
structure IgnoranceVsScalarDatum where
  /-- The utterance -/
  utterance : String
  /-- Type of inference -/
  inferenceType : String
  /-- The inference -/
  inference : String
  /-- Is speaker claiming knowledge? -/
  speakerClaimsKnowledge : Bool
  deriving Repr

/--
"Some" triggers scalar implicature (speaker knows).
-/
def someScalar : IgnoranceVsScalarDatum :=
  { utterance := "Some students passed"
  , inferenceType := "scalar"
  , inference := "Speaker believes not all students passed"
  , speakerClaimsKnowledge := true  -- Speaker KNOWS not all
  }

/--
"Or" triggers ignorance (speaker doesn't know).
-/
def orIgnorance : IgnoranceVsScalarDatum :=
  { utterance := "John passed or Mary passed"
  , inferenceType := "ignorance"
  , inference := "Speaker doesn't know which one passed"
  , speakerClaimsKnowledge := false  -- Speaker DOESN'T KNOW
  }

/--
All comparison examples.
-/
def comparisonExamples : List IgnoranceVsScalarDatum :=
  [someScalar, orIgnorance]

-- ============================================================================
-- PART 3: Long Disjunction Ignorance
-- ============================================================================

/--
Ignorance extends to long disjunctions (n > 2).

For "A or B or C", we get ignorance about each disjunct:
- Speaker doesn't know A
- Speaker doesn't know B
- Speaker doesn't know C

Source: Geurts (2010) p.61-64
-/
structure LongDisjunctionIgnoranceDatum where
  /-- The disjunctive statement -/
  disjunction : String
  /-- List of disjuncts -/
  disjuncts : List String
  /-- Ignorance inferences (one per disjunct) -/
  ignoranceInferences : List String
  deriving Repr

/--
Three-way disjunction example.
Source: Geurts (2010) p.61
-/
def threeWayLocation : LongDisjunctionIgnoranceDatum :=
  { disjunction := "Harry is in Antwerp, Brussels, or Copenhagen"
  , disjuncts := ["Antwerp", "Brussels", "Copenhagen"]
  , ignoranceInferences :=
      [ "Speaker doesn't know Harry is in Antwerp"
      , "Speaker doesn't know Harry is in Brussels"
      , "Speaker doesn't know Harry is in Copenhagen"
      ]
  }

/--
Four-way disjunction example.
-/
def fourWayActivity : LongDisjunctionIgnoranceDatum :=
  { disjunction := "John is reading, writing, sleeping, or eating"
  , disjuncts := ["reading", "writing", "sleeping", "eating"]
  , ignoranceInferences :=
      [ "Speaker doesn't know John is reading"
      , "Speaker doesn't know John is writing"
      , "Speaker doesn't know John is sleeping"
      , "Speaker doesn't know John is eating"
      ]
  }

/--
All long disjunction examples.
-/
def longDisjunctionExamples : List LongDisjunctionIgnoranceDatum :=
  [threeWayLocation, fourWayActivity]

-- ============================================================================
-- PART 4: Ignorance Blocking
-- ============================================================================

/--
Cases where ignorance inference is blocked or cancelled.
-/
structure IgnoranceBlockingDatum where
  /-- The context or construction -/
  context : String
  /-- Example sentence -/
  sentence : String
  /-- Is ignorance blocked? -/
  ignoranceBlocked : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

/--
Explicit knowledge blocks ignorance.
-/
def explicitKnowledge : IgnoranceBlockingDatum :=
  { context := "Speaker has explicit knowledge"
  , sentence := "Harry is in Antwerp or Brussels — I know it's Antwerp"
  , ignoranceBlocked := true
  , explanation := "Explicit assertion of knowledge cancels ignorance inference"
  }

/--
Rhetorical questions don't trigger ignorance.
-/
def rhetoricalQuestion : IgnoranceBlockingDatum :=
  { context := "Rhetorical/exam question"
  , sentence := "Is the capital of France Paris or London?"
  , ignoranceBlocked := true
  , explanation := "Speaker (examiner) knows the answer; no genuine ignorance"
  }

/--
Embedded disjunction under belief.
-/
def embeddedBelief : IgnoranceBlockingDatum :=
  { context := "Embedded under belief verb"
  , sentence := "John believes Harry is in Antwerp or Brussels"
  , ignoranceBlocked := true
  , explanation := "Ignorance is about John's epistemic state, not speaker's"
  }

/--
All blocking examples.
-/
def blockingExamples : List IgnoranceBlockingDatum :=
  [explicitKnowledge, rhetoricalQuestion, embeddedBelief]

-- ============================================================================
-- PART 5: Ignorance with Quantifiers
-- ============================================================================

/--
Interaction between disjunction ignorance and quantifiers.
-/
structure QuantifiedIgnoranceDatum where
  /-- The sentence -/
  sentence : String
  /-- Quantifier scope -/
  quantifierScope : String
  /-- Ignorance inference -/
  inference : String
  /-- Notes on the reading -/
  notes : String
  deriving Repr

/--
Disjunction in scope of universal.
-/
def universalScopeDisj : QuantifiedIgnoranceDatum :=
  { sentence := "Every student read Moby Dick or Huckleberry Finn"
  , quantifierScope := "∀ > ∨"
  , inference := "Speaker doesn't know which book each student read"
  , notes := "Ignorance is about the distribution, not existence"
  }

/--
Disjunction scoping over universal.
-/
def disjScopeUniversal : QuantifiedIgnoranceDatum :=
  { sentence := "Every student read Moby Dick, or every student read Huckleberry Finn"
  , quantifierScope := "∨ > ∀"
  , inference := "Speaker doesn't know which book ALL students read"
  , notes := "Global ignorance about which alternative"
  }

/--
All quantified ignorance examples.
-/
def quantifiedIgnoranceExamples : List QuantifiedIgnoranceDatum :=
  [universalScopeDisj, disjScopeUniversal]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `DisjunctionIgnoranceDatum`: Basic ignorance pattern
- `IgnoranceVsScalarDatum`: Comparison with scalar implicatures
- `LongDisjunctionIgnoranceDatum`: Ignorance with n>2 disjuncts
- `IgnoranceBlockingDatum`: Cases where ignorance is blocked
- `QuantifiedIgnoranceDatum`: Interaction with quantifiers

### Example Collections
- `disjunctionIgnoranceExamples`: 3 basic examples
- `comparisonExamples`: 2 scalar vs ignorance examples
- `longDisjunctionExamples`: 2 long disjunction examples
- `blockingExamples`: 3 blocking contexts
- `quantifiedIgnoranceExamples`: 2 quantifier interactions

### Key References
- Gazdar (1979): Original observation
- Sauerland (2004): Compositional analysis
- Geurts (2010): Modern synthesis
-/

end Phenomena.DisjunctionIgnorance
