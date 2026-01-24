/-
# Scalar Implicatures: Empirical Data

Theory-neutral empirical patterns for scalar implicatures.

## Phenomena Covered

1. **DE Blocking**: Scalar implicatures blocked in downward-entailing contexts
2. **Weak vs Strong**: ¬Bel_S(ψ) vs Bel_S(¬ψ) distinction

## Key References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Gazdar, G. (1979). Pragmatics: Implicature, Presupposition, and Logical Form.
- Geurts, B. (2010). Quantity Implicatures. Cambridge University Press. Ch. 2-3.
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
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `DEBlockingDatum`: DE context blocking pattern
- `WeakStrongDatum`: Weak vs strong implicature pattern
- `HornScaleDatum`: Horn scale with examples

### Example Collections
- `deBlockingExamples`: 4 examples (some/all, or/and, possible/necessary, every-restrictor)
- `weakStrongExamples`: 3 examples (some, or, numerals)
- `hornScaleExamples`: 4 scales (quantifiers, connectives, modals, numerals)

### Key References
- Horn (1972): Original scale proposal
- Gazdar (1979): Weak vs strong distinction
- Ladusaw (1980): DE environments
- Soames (1982): Competence assumption
- Geurts (2010): Modern synthesis
-/

end Phenomena.ScalarImplicatures
