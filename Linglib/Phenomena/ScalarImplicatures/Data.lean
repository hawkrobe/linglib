/-
# Scalar Implicatures: Empirical Data

Theory-neutral empirical patterns for scalar implicatures.

## Phenomena Covered

1. **DE Blocking**: Scalar implicatures blocked in downward-entailing contexts
2. **Weak vs Strong**: ¬Bel_S(ψ) vs Bel_S(¬ψ) distinction
3. **Horn Scales**: Scale examples with implicatures
4. **Hurford's Constraint**: Entailing disjunctions and rescue by exhaustification
5. **Singh's Asymmetry**: Order effects in scalar disjunctions

## Key References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Hurford, J. (1974). Exclusive or inclusive disjunction. Foundations of Language.
- Gazdar, G. (1979). Pragmatics: Implicature, Presupposition, and Logical Form.
- Singh, R. (2008). On the interpretation of disjunction.
- Geurts, B. (2010). Quantity Implicatures. Cambridge University Press. Ch. 2-3.
- Fox & Spector (2018). Economy and embedded exhaustification.
-/

namespace Phenomena.ScalarImplicatures

-- ============================================================================
-- PART 1: DE Blocking Data
-- ============================================================================

/--
Empirical pattern: Scalar implicatures in DE contexts.

In upward-entailing (UE) contexts, "some" implicates "not all".
In downward-entailing (DE) contexts, this implicature is BLOCKED.

Examples:
- UE: "John ate some cookies" → "not all cookies"
- DE: "No one ate some cookies" → NO "not all" implicature
-/
structure DEBlockingDatum where
  /-- Example in UE context -/
  ueExample : String
  /-- Example in DE context -/
  deExample : String
  /-- Scalar term used -/
  scalarTerm : String
  /-- Stronger alternative on the scale -/
  strongerAlt : String
  /-- Does the implicature arise in UE? -/
  implicatureInUE : Bool
  /-- Does the implicature arise in DE? -/
  implicatureInDE : Bool
  deriving Repr

/--
Classic example: "some" in DE blocks "not all" implicature.
Source: Ladusaw (1980), Geurts (2010) Ch. 3.2
-/
def someAllBlocking : DEBlockingDatum :=
  { ueExample := "John ate some of the cookies"
  , deExample := "No one ate some of the cookies"
  , scalarTerm := "some"
  , strongerAlt := "all"
  , implicatureInUE := true   -- "not all" implicature arises
  , implicatureInDE := false  -- "not all" implicature BLOCKED
  }

/--
"or" in DE blocks "not and" implicature.
Source: Geurts (2010) Ch. 3.2
-/
def orAndBlocking : DEBlockingDatum :=
  { ueExample := "John ate cake or pie"
  , deExample := "No one ate cake or pie"
  , scalarTerm := "or"
  , strongerAlt := "and"
  , implicatureInUE := true   -- "not both" implicature arises
  , implicatureInDE := false  -- "not both" implicature BLOCKED
  }

/--
"possible" in DE contexts.
Source: Horn (1989)
-/
def possibleNecessaryBlocking : DEBlockingDatum :=
  { ueExample := "It's possible that John will come"
  , deExample := "It's not the case that it's possible that John will come"
  , scalarTerm := "possible"
  , strongerAlt := "necessary"
  , implicatureInUE := true   -- "not necessary" implicature
  , implicatureInDE := false  -- blocked
  }

/--
Restrictor of "every" is DE.
Source: Ladusaw (1980), Barwise & Cooper (1981)
-/
def everyRestrictorDE : DEBlockingDatum :=
  { ueExample := "Every student who solved some problems passed"
  , deExample := "Every student who solved some problems passed"  -- restrictor is DE
  , scalarTerm := "some"
  , strongerAlt := "all"
  , implicatureInUE := true
  , implicatureInDE := false  -- blocked in restrictor position
  }

/--
All DE blocking examples.
-/
def deBlockingExamples : List DEBlockingDatum :=
  [someAllBlocking, orAndBlocking, possibleNecessaryBlocking, everyRestrictorDE]

-- ============================================================================
-- PART 2: Weak vs Strong Implicature Data
-- ============================================================================

/--
Empirical pattern: Weak vs strong implicatures.

From "some students came":
- Weak: Speaker doesn't believe all came (¬Bel_S(all))
- Strong: Speaker believes not all came (Bel_S(¬all))

The strong requires COMPETENCE assumption.

Source: Soames (1982), Geurts (2010) Ch. 2.3
-/
structure WeakStrongDatum where
  /-- The utterance -/
  utterance : String
  /-- The scalar alternative -/
  alternative : String
  /-- Weak implicature description -/
  weakImplicature : String
  /-- Strong implicature description -/
  strongImplicature : String
  /-- Does weak require competence? -/
  weakRequiresCompetence : Bool
  /-- Does strong require competence? -/
  strongRequiresCompetence : Bool
  deriving Repr

/--
Classic "some" example.
Source: Horn (1972), Geurts (2010) Ch. 2.3
-/
def someStudents : WeakStrongDatum :=
  { utterance := "Some students came"
  , alternative := "All students came"
  , weakImplicature := "Speaker doesn't believe all students came"
  , strongImplicature := "Speaker believes not all students came"
  , weakRequiresCompetence := false  -- Weak always derivable
  , strongRequiresCompetence := true -- Strong needs competence
  }

/--
"Or" example showing weak vs strong.
Source: Gazdar (1979)
-/
def orWeakStrong : WeakStrongDatum :=
  { utterance := "John ate cake or pie"
  , alternative := "John ate cake and pie"
  , weakImplicature := "Speaker doesn't believe John ate both"
  , strongImplicature := "Speaker believes John didn't eat both"
  , weakRequiresCompetence := false
  , strongRequiresCompetence := true
  }

/--
Numeral example.
Source: Horn (1972)
-/
def numeralWeakStrong : WeakStrongDatum :=
  { utterance := "John has three children"
  , alternative := "John has four children"
  , weakImplicature := "Speaker doesn't believe John has four children"
  , strongImplicature := "Speaker believes John doesn't have four children"
  , weakRequiresCompetence := false
  , strongRequiresCompetence := true
  }

/--
All weak/strong examples.
-/
def weakStrongExamples : List WeakStrongDatum :=
  [someStudents, orWeakStrong, numeralWeakStrong]

-- ============================================================================
-- PART 3: Horn Scales Data
-- ============================================================================

/--
A Horn scale with its members and example implicatures.
Source: Horn (1972)
-/
structure HornScaleDatum where
  /-- Name of the scale -/
  name : String
  /-- Members from weakest to strongest -/
  members : List String
  /-- Example sentence with weakest term -/
  exampleSentence : String
  /-- Resulting implicature -/
  implicature : String
  deriving Repr

/--
Quantifier scale.
Source: Horn (1972)
-/
def quantifierScale : HornScaleDatum :=
  { name := "Quantifiers"
  , members := ["some", "most", "all"]
  , exampleSentence := "Some students passed"
  , implicature := "Not all students passed"
  }

/--
Connective scale.
Source: Horn (1972)
-/
def connectiveScale : HornScaleDatum :=
  { name := "Connectives"
  , members := ["or", "and"]
  , exampleSentence := "John sang or danced"
  , implicature := "John didn't both sing and dance"
  }

/--
Modal scale.
Source: Horn (1972)
-/
def modalScale : HornScaleDatum :=
  { name := "Modals"
  , members := ["possible", "necessary"]
  , exampleSentence := "It's possible that it will rain"
  , implicature := "It's not necessary that it will rain"
  }

/--
Numeral scale (with lower-bound semantics).
Source: Horn (1972)
-/
def numeralScale : HornScaleDatum :=
  { name := "Numerals"
  , members := ["one", "two", "three", "four", "five"]
  , exampleSentence := "John has two children"
  , implicature := "John doesn't have three (or more) children"
  }

/--
All Horn scale examples.
-/
def hornScaleExamples : List HornScaleDatum :=
  [quantifierScale, connectiveScale, modalScale, numeralScale]

-- ============================================================================
-- PART 4: Scale Example Structure (from Scales.lean)
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
A Horn scale datum with weaker/stronger terms (string-level).
-/
structure HornScaleDatumPair where
  /-- Name of the scale -/
  name : String
  /-- The weaker scalar term (e.g., "some") -/
  weakerTerm : String
  /-- The stronger scalar term (e.g., "all") -/
  strongerTerm : String
  /-- Example sentence -/
  exampleSentence : ScaleExample
  deriving Repr

/-- Example: "Some students passed" -/
def someAllExample : ScaleExample :=
  { sentence := "Some students passed"
  , implicature := "Not all students passed"
  , arisesInUE := true
  }

/-- The some/all scale datum. -/
def someAllDatum : HornScaleDatumPair :=
  { name := "Quantifiers (some/all)"
  , weakerTerm := "some"
  , strongerTerm := "all"
  , exampleSentence := someAllExample
  }

/-- Example: "John sang or danced" -/
def orAndExample : ScaleExample :=
  { sentence := "John sang or danced"
  , implicature := "John didn't both sing and dance"
  , arisesInUE := true
  }

/-- The or/and scale datum. -/
def orAndDatum : HornScaleDatumPair :=
  { name := "Connectives (or/and)"
  , weakerTerm := "or"
  , strongerTerm := "and"
  , exampleSentence := orAndExample
  }

/-- Example: "It's possible it will rain" -/
def possibleNecessaryExample : ScaleExample :=
  { sentence := "It's possible that it will rain"
  , implicature := "It's not necessary that it will rain"
  , arisesInUE := true
  }

/-- The possible/necessary scale datum. -/
def possibleNecessaryDatum : HornScaleDatumPair :=
  { name := "Modals (possible/necessary)"
  , weakerTerm := "possible"
  , strongerTerm := "necessary"
  , exampleSentence := possibleNecessaryExample
  }

/-- All scale examples (string-level). -/
def allScaleExamples : List ScaleExample :=
  [someAllExample, orAndExample, possibleNecessaryExample]

/-- All Horn scale pair data. -/
def allScalePairs : List HornScaleDatumPair :=
  [someAllDatum, orAndDatum, possibleNecessaryDatum]

/-- All examples arise in UE contexts. -/
theorem all_arise_in_UE : allScaleExamples.all (·.arisesInUE) := by native_decide

-- ============================================================================
-- PART 5: Hurford's Constraint Data
-- ============================================================================

/--
A potential Hurford violation: a disjunction "A or B" where
one disjunct entails the other.
-/
structure HurfordDatum where
  /-- The disjunction sentence -/
  sentence : String
  /-- First disjunct -/
  disjunctA : String
  /-- Second disjunct -/
  disjunctB : String
  /-- Which direction is the entailment? -/
  entailmentDirection : String  -- "A ⊆ B" or "B ⊆ A"
  /-- Is the sentence felicitous? -/
  felicitous : Bool
  /-- If felicitous, how is it rescued? -/
  rescueMethod : Option String
  deriving Repr

/--
Classic Hurford violation: hyponym or hypernym.
"#John is American or Californian" — Californian entails American.
-/
def americanCalifornian : HurfordDatum :=
  { sentence := "#John is American or Californian"
  , disjunctA := "American"
  , disjunctB := "Californian"
  , entailmentDirection := "B ⊆ A"  -- Californian ⊆ American
  , felicitous := false
  , rescueMethod := none
  }

/--
"#John is a bachelor or unmarried" — bachelor entails unmarried.
-/
def bachelorUnmarried : HurfordDatum :=
  { sentence := "#John is a bachelor or unmarried"
  , disjunctA := "bachelor"
  , disjunctB := "unmarried"
  , entailmentDirection := "A ⊆ B"  -- bachelor ⊆ unmarried
  , felicitous := false
  , rescueMethod := none
  }

/--
"#The number is even or divisible by 2"
-/
def evenDivisibleBy2 : HurfordDatum :=
  { sentence := "#The number is even or divisible by 2"
  , disjunctA := "even"
  , disjunctB := "divisible by 2"
  , entailmentDirection := "A = B"  -- equivalent
  , felicitous := false
  , rescueMethod := none
  }

/--
Rescued by exhaustification: "some or all".
exh(some) = "some but not all", which doesn't entail "all".
-/
def someOrAll : HurfordDatum :=
  { sentence := "Mary read some or all of the books"
  , disjunctA := "some"
  , disjunctB := "all"
  , entailmentDirection := "B ⊆ A"  -- all ⊆ some (before exh)
  , felicitous := true
  , rescueMethod := some "exh(some) = some but not all"
  }

/--
Rescued: "possible or necessary".
exh(possible) = "possible but not necessary", doesn't entail "necessary".
-/
def possibleOrNecessary : HurfordDatum :=
  { sentence := "It's possible or even necessary that John will come"
  , disjunctA := "possible"
  , disjunctB := "necessary"
  , entailmentDirection := "B ⊆ A"  -- necessary ⊆ possible
  , felicitous := true
  , rescueMethod := some "exh(possible) breaks entailment"
  }

/--
Rescued: "three or all" (distant entailing disjunction).
exh(three) = "exactly three", which doesn't entail "all".
-/
def threeOrAll : HurfordDatum :=
  { sentence := "John solved three or all of the problems"
  , disjunctA := "three"
  , disjunctB := "all"
  , entailmentDirection := "B ⊆ A"  -- all ⊆ at-least-three
  , felicitous := true
  , rescueMethod := some "exh(three) = exactly three"
  }

/-- Infelicitous Hurford violations. -/
def hurfordViolations : List HurfordDatum :=
  [americanCalifornian, bachelorUnmarried, evenDivisibleBy2]

/-- Felicitous (rescued) cases. -/
def hurfordRescuedCases : List HurfordDatum :=
  [someOrAll, possibleOrNecessary, threeOrAll]

/-- All Hurford data. -/
def allHurfordData : List HurfordDatum :=
  hurfordViolations ++ hurfordRescuedCases

/-- All violations are infelicitous. -/
theorem hurford_violations_infelicitous : hurfordViolations.all (·.felicitous == false) := by
  native_decide

/-- All rescued cases are felicitous. -/
theorem hurford_rescued_felicitous : hurfordRescuedCases.all (·.felicitous == true) := by
  native_decide

/-- All rescued cases have a rescue method. -/
theorem hurford_rescued_have_method : hurfordRescuedCases.all (·.rescueMethod.isSome) := by
  native_decide

-- ============================================================================
-- PART 6: Singh's Asymmetry Data
-- ============================================================================

/--
A Singh-style disjunction where one disjunct is stronger than the other.
-/
structure SinghDatum where
  /-- The full sentence -/
  sentence : String
  /-- The weaker disjunct (e.g., "A or B") -/
  weakerDisjunct : String
  /-- The stronger disjunct (e.g., "A and B" / "both") -/
  strongerDisjunct : String
  /-- Is the weaker mentioned first? -/
  weakerFirst : Bool
  /-- Is the sentence felicitous? -/
  felicitous : Bool
  deriving Repr

/--
Classic Singh example: weak-first is OK.
"Mary solved problem A or B, or both"
-/
def orThenBoth : SinghDatum :=
  { sentence := "Mary solved problem A or problem B, or both"
  , weakerDisjunct := "A or B"
  , strongerDisjunct := "both"
  , weakerFirst := true
  , felicitous := true
  }

/--
"John ate cake or pie, or both"
-/
def cakeOrPieOrBoth : SinghDatum :=
  { sentence := "John ate cake or pie, or both"
  , weakerDisjunct := "cake or pie"
  , strongerDisjunct := "both"
  , weakerFirst := true
  , felicitous := true
  }

/--
"It's possible or necessary that it will rain"
-/
def singhPossibleOrNecessary : SinghDatum :=
  { sentence := "It's possible or even necessary that it will rain"
  , weakerDisjunct := "possible"
  , strongerDisjunct := "necessary"
  , weakerFirst := true
  , felicitous := true
  }

/--
Strong-first is odd: "#both, or A or B"
-/
def bothThenOr : SinghDatum :=
  { sentence := "#Mary solved both, or problem A or problem B"
  , weakerDisjunct := "A or B"
  , strongerDisjunct := "both"
  , weakerFirst := false
  , felicitous := false
  }

/--
"#John ate both, or cake or pie"
-/
def bothThenCakeOrPie : SinghDatum :=
  { sentence := "#John ate both, or cake or pie"
  , weakerDisjunct := "cake or pie"
  , strongerDisjunct := "both"
  , weakerFirst := false
  , felicitous := false
  }

/--
"#It's necessary or possible that it will rain"
(Strong-first with modals)
-/
def necessaryOrPossible : SinghDatum :=
  { sentence := "?It's necessary or at least possible that it will rain"
  , weakerDisjunct := "possible"
  , strongerDisjunct := "necessary"
  , weakerFirst := false
  , felicitous := false  -- degraded, though "at least" helps
  }

/-- Weak-first (felicitous) cases. -/
def singhWeakFirstCases : List SinghDatum :=
  [orThenBoth, cakeOrPieOrBoth, singhPossibleOrNecessary]

/-- Strong-first (infelicitous) cases. -/
def singhStrongFirstCases : List SinghDatum :=
  [bothThenOr, bothThenCakeOrPie, necessaryOrPossible]

/-- All Singh data. -/
def allSinghData : List SinghDatum :=
  singhWeakFirstCases ++ singhStrongFirstCases

/-- Weak-first cases are felicitous. -/
theorem singh_weakFirst_felicitous : singhWeakFirstCases.all (·.felicitous == true) := by
  native_decide

/-- Strong-first cases are infelicitous. -/
theorem singh_strongFirst_infelicitous : singhStrongFirstCases.all (·.felicitous == false) := by
  native_decide

/-- All weak-first cases have weakerFirst = true. -/
theorem singh_weakFirst_order : singhWeakFirstCases.all (·.weakerFirst == true) := by
  native_decide

/-- All strong-first cases have weakerFirst = false. -/
theorem singh_strongFirst_order : singhStrongFirstCases.all (·.weakerFirst == false) := by
  native_decide

/--
**The Singh Asymmetry**: felicitous ↔ weakerFirst
(at the data level; theory explains WHY)
-/
theorem singh_asymmetry :
    allSinghData.all (fun d => d.felicitous == d.weakerFirst) := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `DEBlockingDatum`: DE context blocking pattern
- `WeakStrongDatum`: Weak vs strong implicature pattern
- `HornScaleDatum`: Horn scale with examples
- `ScaleExample`: Example sentence with implicature
- `HornScaleDatumPair`: Scale with weaker/stronger terms
- `HurfordDatum`: Hurford's constraint data
- `SinghDatum`: Singh's asymmetry data

### Example Collections
- `deBlockingExamples`: 4 examples (some/all, or/and, possible/necessary, every-restrictor)
- `weakStrongExamples`: 3 examples (some, or, numerals)
- `hornScaleExamples`: 4 scales (quantifiers, connectives, modals, numerals)
- `allScalePairs`: 3 scale pairs (some/all, or/and, possible/necessary)
- `allHurfordData`: 6 examples (3 violations, 3 rescued)
- `allSinghData`: 6 examples (3 weak-first, 3 strong-first)

### Theorems About the Data
- `all_arise_in_UE`: All scale examples arise in UE contexts
- `hurford_violations_infelicitous`: Violations are infelicitous
- `hurford_rescued_felicitous`: Rescued cases are felicitous
- `singh_asymmetry`: felicitous ↔ weakerFirst

### Key References
- Horn (1972): Original scale proposal
- Hurford (1974): Hurford's constraint
- Gazdar (1979): Weak vs strong distinction
- Ladusaw (1980): DE environments
- Soames (1982): Competence assumption
- Singh (2008): Order asymmetry
- Geurts (2010): Modern synthesis
- Fox & Spector (2018): Economy and embedded exhaustification
-/

end Phenomena.ScalarImplicatures
