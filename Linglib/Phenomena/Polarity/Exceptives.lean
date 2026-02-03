/-
# But-Exceptive Data

Empirical patterns for "X but Y" exceptive constructions.

## Key Pattern (von Fintel 1993)

But-exceptives require UNIVERSAL quantifiers (positive or negative):

| Quantifier | Example | Grammatical |
|------------|---------|-------------|
| every | "everyone but John" | ✓ |
| no | "no one but John" | ✓ |
| some | "*someone but John" | ✗ |
| many | "*many people but John" | ✗ |
| few | "*few people but John" | ✗ |

## Semantic Contribution

The but-exceptive:
1. Subtracts the exception from the quantifier's domain
2. Presupposes/asserts that WITHOUT the exception, the claim would be false

## Theoretical Analysis

See:
- `Core/Analyticity.lean`: L-analyticity explanation (Gajewski 2002)
- The semantics should go in `Theories/Montague/Lexicon/` when added

## References

- von Fintel, K. (1993). Exceptive constructions. NLLT 11(1):123-148.
- Hoeksema, J. (1995). The semantics of exception phrases.
- Gajewski, J. (2002). On analyticity in natural language.
- Moltmann, F. (1995). Exception sentences and polyadic quantification.
-/

namespace Phenomena.Polarity.Exceptives

-- ============================================================================
-- PART 1: Quantifier Compatibility
-- ============================================================================

/--
Type of quantifier for exceptive compatibility.
-/
inductive QuantifierType where
  | universalPositive   -- every, all, each
  | universalNegative   -- no, none
  | existential         -- some, a, several
  | proportional        -- most, many, few
  | numeral             -- two, three, exactly five
  deriving DecidableEq, BEq, Repr

/--
But-exceptive example with grammaticality judgment.
-/
structure ButExceptiveExample where
  /-- The quantifier used -/
  quantifier : String
  /-- Type of quantifier -/
  quantifierType : QuantifierType
  /-- The sentence -/
  sentence : String
  /-- Is it grammatical? -/
  grammatical : Bool
  /-- Notes -/
  notes : String
  deriving Repr

-- Universal positive quantifiers: grammatical
def every_but_john : ButExceptiveExample :=
  { quantifier := "every"
  , quantifierType := .universalPositive
  , sentence := "Every student but John passed"
  , grammatical := true
  , notes := "Universal positive: OK" }

def all_but_mary : ButExceptiveExample :=
  { quantifier := "all"
  , quantifierType := .universalPositive
  , sentence := "All students but Mary attended"
  , grammatical := true
  , notes := "Universal positive: OK" }

def each_but_sue : ButExceptiveExample :=
  { quantifier := "each"
  , quantifierType := .universalPositive
  , sentence := "Each student but Sue submitted the homework"
  , grammatical := true
  , notes := "Universal positive: OK" }

-- Universal negative quantifiers: grammatical
def no_one_but_john : ButExceptiveExample :=
  { quantifier := "no one"
  , quantifierType := .universalNegative
  , sentence := "No one but John passed"
  , grammatical := true
  , notes := "Universal negative: OK" }

def none_but_mary : ButExceptiveExample :=
  { quantifier := "none"
  , quantifierType := .universalNegative
  , sentence := "None of the students but Mary attended"
  , grammatical := true
  , notes := "Universal negative: OK" }

-- Existential quantifiers: ungrammatical
def some_but_john : ButExceptiveExample :=
  { quantifier := "some"
  , quantifierType := .existential
  , sentence := "*Some student but John passed"
  , grammatical := false
  , notes := "Existential: blocked (L-contradictory)" }

def a_but_mary : ButExceptiveExample :=
  { quantifier := "a"
  , quantifierType := .existential
  , sentence := "*A student but Mary attended"
  , grammatical := false
  , notes := "Existential: blocked" }

def several_but_sue : ButExceptiveExample :=
  { quantifier := "several"
  , quantifierType := .existential
  , sentence := "*Several students but Sue passed"
  , grammatical := false
  , notes := "Existential (plural): blocked" }

-- Proportional quantifiers: ungrammatical
def most_but_john : ButExceptiveExample :=
  { quantifier := "most"
  , quantifierType := .proportional
  , sentence := "*Most students but John passed"
  , grammatical := false
  , notes := "Proportional: blocked" }

def many_but_mary : ButExceptiveExample :=
  { quantifier := "many"
  , quantifierType := .proportional
  , sentence := "*Many students but Mary attended"
  , grammatical := false
  , notes := "Proportional: blocked" }

def few_but_sue : ButExceptiveExample :=
  { quantifier := "few"
  , quantifierType := .proportional
  , sentence := "*Few students but Sue passed"
  , grammatical := false
  , notes := "Proportional: blocked" }

-- Numeral quantifiers: ungrammatical
def two_but_john : ButExceptiveExample :=
  { quantifier := "two"
  , quantifierType := .numeral
  , sentence := "*Two students but John passed"
  , grammatical := false
  , notes := "Numeral: blocked" }

def exactly_five_but : ButExceptiveExample :=
  { quantifier := "exactly five"
  , quantifierType := .numeral
  , sentence := "*Exactly five students but John passed"
  , grammatical := false
  , notes := "Numeral: blocked" }

/--
All but-exceptive examples.
-/
def butExceptiveExamples : List ButExceptiveExample :=
  [ every_but_john, all_but_mary, each_but_sue
  , no_one_but_john, none_but_mary
  , some_but_john, a_but_mary, several_but_sue
  , most_but_john, many_but_mary, few_but_sue
  , two_but_john, exactly_five_but
  ]

-- Verify: universal quantifiers license exceptives
#guard butExceptiveExamples.filter (fun ex =>
  ex.quantifierType == .universalPositive || ex.quantifierType == .universalNegative)
  |>.all (fun ex => ex.grammatical)

-- Verify: non-universal quantifiers block exceptives
#guard butExceptiveExamples.filter (fun ex =>
  ex.quantifierType != .universalPositive && ex.quantifierType != .universalNegative)
  |>.all (fun ex => !ex.grammatical)

-- ============================================================================
-- PART 2: Semantic Properties
-- ============================================================================

/--
Predict grammaticality from quantifier type.

The generalization: only UNIVERSAL quantifiers (positive or negative)
license but-exceptives.
-/
def predictExceptiveGrammaticality (qt : QuantifierType) : Bool :=
  match qt with
  | .universalPositive => true
  | .universalNegative => true
  | .existential => false
  | .proportional => false
  | .numeral => false

-- Verify predictions match data
#guard butExceptiveExamples.all (fun ex =>
  predictExceptiveGrammaticality ex.quantifierType == ex.grammatical)

-- ============================================================================
-- PART 3: Exception Uniqueness
-- ============================================================================

/-!
## Exception Uniqueness

The but-exceptive typically requires that the exception be UNIQUE:

✓ "Everyone but John passed" (one exception)
? "Everyone but John and Mary passed" (multiple exceptions)

The multiple-exception case is degraded or requires special interpretation.
-/

/--
Data on exception cardinality.
-/
structure ExceptionCardinalityExample where
  /-- The sentence -/
  sentence : String
  /-- Number of exceptions -/
  numExceptions : Nat
  /-- Acceptability (1-5 scale) -/
  acceptability : Nat
  /-- Notes -/
  notes : String
  deriving Repr

def single_exception : ExceptionCardinalityExample :=
  { sentence := "Everyone but John passed"
  , numExceptions := 1
  , acceptability := 5
  , notes := "Single exception: fully acceptable" }

def two_exceptions : ExceptionCardinalityExample :=
  { sentence := "Everyone but John and Mary passed"
  , numExceptions := 2
  , acceptability := 3
  , notes := "Two exceptions: degraded, requires list interpretation" }

def three_exceptions : ExceptionCardinalityExample :=
  { sentence := "Everyone but John, Mary, and Sue passed"
  , numExceptions := 3
  , acceptability := 2
  , notes := "Three exceptions: further degraded" }

/--
All exception cardinality examples.
-/
def exceptionCardinalityExamples : List ExceptionCardinalityExample :=
  [single_exception, two_exceptions, three_exceptions]

-- ============================================================================
-- PART 4: Cross-linguistic Data
-- ============================================================================

/--
Cross-linguistic but-exceptive data.
-/
structure CrossLinguisticExceptive where
  /-- Language -/
  language : String
  /-- Exceptive morpheme -/
  exceptiveMorpheme : String
  /-- Example sentence -/
  exampleSentence : String
  /-- Gloss -/
  gloss : String
  /-- Same universal constraint? -/
  universalConstraint : Bool
  deriving Repr

def english_but : CrossLinguisticExceptive :=
  { language := "English"
  , exceptiveMorpheme := "but"
  , exampleSentence := "Everyone but John passed"
  , gloss := "every-one but John passed"
  , universalConstraint := true }

def german_ausser : CrossLinguisticExceptive :=
  { language := "German"
  , exceptiveMorpheme := "außer"
  , exampleSentence := "Jeder außer Hans hat bestanden"
  , gloss := "everyone except Hans has passed"
  , universalConstraint := true }

def french_sauf : CrossLinguisticExceptive :=
  { language := "French"
  , exceptiveMorpheme := "sauf"
  , exampleSentence := "Tout le monde sauf Jean a réussi"
  , gloss := "everyone except Jean has succeeded"
  , universalConstraint := true }

def spanish_excepto : CrossLinguisticExceptive :=
  { language := "Spanish"
  , exceptiveMorpheme := "excepto"
  , exampleSentence := "Todos excepto Juan aprobaron"
  , gloss := "everyone except Juan passed"
  , universalConstraint := true }

/--
All cross-linguistic examples.
-/
def crossLinguisticExamples : List CrossLinguisticExceptive :=
  [english_but, german_ausser, french_sauf, spanish_excepto]

-- Universal constraint appears cross-linguistically
#guard crossLinguisticExamples.all (fun ex => ex.universalConstraint)

-- ============================================================================
-- PART 5: Related Constructions
-- ============================================================================

/--
Related exceptive-like constructions.
-/
inductive ExceptiveConstruction where
  | butExceptive       -- "everyone but John"
  | exceptExceptive    -- "everyone except John"
  | otherThan          -- "everyone other than John"
  | besidesExceptive   -- "everyone besides John"
  deriving DecidableEq, BEq, Repr

/--
Comparison of exceptive constructions.
-/
structure ExceptiveConstructionExample where
  /-- Construction type -/
  construction : ExceptiveConstruction
  /-- Example -/
  exampleSentence : String
  /-- Same universal constraint? -/
  hasUniversalConstraint : Bool
  /-- Additional notes -/
  notes : String
  deriving Repr

def but_construction : ExceptiveConstructionExample :=
  { construction := .butExceptive
  , exampleSentence := "Everyone but John passed"
  , hasUniversalConstraint := true
  , notes := "Strict universal requirement" }

def except_construction : ExceptiveConstructionExample :=
  { construction := .exceptExceptive
  , exampleSentence := "Everyone except John passed"
  , hasUniversalConstraint := true
  , notes := "Similar to 'but'" }

def other_than_construction : ExceptiveConstructionExample :=
  { construction := .otherThan
  , exampleSentence := "Everyone other than John passed"
  , hasUniversalConstraint := true
  , notes := "Similar semantics" }

def besides_construction : ExceptiveConstructionExample :=
  { construction := .besidesExceptive
  , exampleSentence := "Everyone besides John passed"
  , hasUniversalConstraint := true
  , notes := "American English variant" }

/--
All exceptive construction examples.
-/
def exceptiveConstructionExamples : List ExceptiveConstructionExample :=
  [but_construction, except_construction, other_than_construction, besides_construction]

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Data Types
- `QuantifierType`: Classification of quantifiers
- `ButExceptiveExample`: Grammaticality data
- `ExceptionCardinalityExample`: Exception count effects
- `CrossLinguisticExceptive`: Cross-linguistic patterns
- `ExceptiveConstructionExample`: Related constructions

### Key Generalizations
1. Only UNIVERSAL quantifiers license but-exceptives
2. Existential, proportional, and numeral quantifiers are blocked
3. The constraint is L-analytic (see Core/Analyticity.lean)
4. The constraint appears cross-linguistically
5. Multiple exceptions degrade acceptability

### Predictions
- `predictExceptiveGrammaticality`: Universal → OK, else → blocked

### References
- von Fintel (1993). Exceptive constructions.
- Gajewski (2002). On analyticity in natural language.
- Hoeksema (1995). The semantics of exception phrases.
-/

end Phenomena.Polarity.Exceptives
