/-
# Horn Scales: Empirical Data

String-level examples of Horn scales and scalar implicatures.
Theory-neutral data for `Theories/NeoGricean/ScaleSemantics.lean` to formalize.

## Key References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Hirschberg, J. (1991). A Theory of Scalar Implicature.
-/

namespace Phenomena.ScalarImplicatures.Scales

-- ============================================================================
-- PART 1: Scale Example Structure
-- ============================================================================

/--
An example sentence demonstrating a scalar implicature.
-/
structure ScaleExample where
  /-- The sentence -/
  sentence : String
  /-- The predicted implicature -/
  implicature : String
  /-- Does the implicature arise in upward-entailing context? -/
  arisesInUE : Bool := true
  deriving Repr

/--
A Horn scale datum (string-level).
-/
structure HornScaleDatum where
  /-- Name of the scale -/
  name : String
  /-- The weaker scalar term (e.g., "some") -/
  weakerTerm : String
  /-- The stronger scalar term (e.g., "all") -/
  strongerTerm : String
  /-- Example sentence -/
  exampleSentence : ScaleExample
  deriving Repr

-- ============================================================================
-- PART 2: SOME/ALL SCALE
-- ============================================================================

/-- Example: "Some students passed" -/
def someAllExample : ScaleExample :=
  { sentence := "Some students passed"
  , implicature := "Not all students passed"
  , arisesInUE := true
  }

/-- The some/all scale datum. -/
def someAllDatum : HornScaleDatum :=
  { name := "Quantifiers (some/all)"
  , weakerTerm := "some"
  , strongerTerm := "all"
  , exampleSentence := someAllExample
  }

-- ============================================================================
-- PART 3: OR/AND SCALE
-- ============================================================================

/-- Example: "John sang or danced" -/
def orAndExample : ScaleExample :=
  { sentence := "John sang or danced"
  , implicature := "John didn't both sing and dance"
  , arisesInUE := true
  }

/-- The or/and scale datum. -/
def orAndDatum : HornScaleDatum :=
  { name := "Connectives (or/and)"
  , weakerTerm := "or"
  , strongerTerm := "and"
  , exampleSentence := orAndExample
  }

-- ============================================================================
-- PART 4: POSSIBLE/NECESSARY SCALE
-- ============================================================================

/-- Example: "It's possible it will rain" -/
def possibleNecessaryExample : ScaleExample :=
  { sentence := "It's possible that it will rain"
  , implicature := "It's not necessary that it will rain"
  , arisesInUE := true
  }

/-- The possible/necessary scale datum. -/
def possibleNecessaryDatum : HornScaleDatum :=
  { name := "Modals (possible/necessary)"
  , weakerTerm := "possible"
  , strongerTerm := "necessary"
  , exampleSentence := possibleNecessaryExample
  }

-- ============================================================================
-- PART 5: COLLECTIONS
-- ============================================================================

/-- All scale examples (string-level). -/
def allExamples : List ScaleExample :=
  [someAllExample, orAndExample, possibleNecessaryExample]

/-- All Horn scale data. -/
def allScales : List HornScaleDatum :=
  [someAllDatum, orAndDatum, possibleNecessaryDatum]

-- ============================================================================
-- PART 6: Basic Theorems About the Data
-- ============================================================================

/-- All examples arise in UE contexts. -/
theorem all_arise_in_UE : allExamples.all (·.arisesInUE) := by native_decide

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## Data Provided

| Scale | Weaker | Stronger | Example |
|-------|--------|----------|---------|
| Quantifiers | some | all | "Some students passed" |
| Connectives | or | and | "John sang or danced" |
| Modals | possible | necessary | "It's possible it will rain" |

## Interface for Theory

`Theories/NeoGricean/ScaleSemantics.lean` provides:
- `HornScale World` with semantic content
- Concrete scales: `someAllScale`, `orAndScale`, `possibleNecessaryScale`
- Entailment proofs: `all_entails_some`, etc.

Theory proves exhaustification derives these implicatures.
-/

end Phenomena.ScalarImplicatures.Scales
