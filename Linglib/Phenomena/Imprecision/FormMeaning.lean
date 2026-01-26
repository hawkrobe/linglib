/-
# Form/Meaning Correspondences: Empirical Data

Theory-neutral empirical patterns relating syntactic complexity to precision.

## Phenomena Covered

1. **Complexity-precision pairs**: "the doors" / "all the doors"
2. **Unattested patterns**: No language has DEF [all doors] → "the doors"
3. **Cross-constructional parallels**: Plurals, numerals, conjunctions

## Key Observation (NO NEEDLESS MANNER VIOLATIONS)

There is a systematic correlation:
- Less complex expressions → more potential for imprecision
- More complex expressions → more precise meanings

The reverse pattern (adding complexity to ADD imprecision) is unattested.

## Key References

- Löbner (2000): Polarity and complexity
- Krifka (2002, 2007): Complexity and imprecision
- Horn (1984): Division of pragmatic labor
- Katzir (2007): Structural complexity and alternatives
- Dissertation Chapter 3: NO NEEDLESS MANNER VIOLATIONS
-/

namespace Phenomena.Imprecision.FormMeaning

-- ============================================================================
-- PART 1: Complexity Ordering
-- ============================================================================

/--
Relative complexity judgment between two expressions.
-/
inductive ComplexityRelation where
  | lessComplex      -- φ is less complex than ψ
  | moreComplex      -- φ is more complex than ψ
  | equalComplexity  -- same complexity
  | incomparable     -- not comparable
  deriving Repr, DecidableEq

/--
Relative precision judgment between two expressions.
-/
inductive PrecisionRelation where
  | lessPrecise    -- φ has more potential for imprecision
  | morePrecise    -- φ has less potential for imprecision
  | equalPrecision -- same precision
  | incomparable   -- not comparable
  deriving Repr, DecidableEq

-- ============================================================================
-- PART 2: Attested Complexity-Precision Pairs
-- ============================================================================

/--
A pair of expressions showing the complexity-precision tradeoff.
-/
structure ComplexityPrecisionPair where
  /-- Less complex expression -/
  lessComplexExpr : String
  /-- More complex expression -/
  moreComplexExpr : String
  /-- What makes it more complex -/
  complexitySource : String
  /-- Does less complex permit imprecision? -/
  lessComplexImprecise : Bool
  /-- Does more complex permit imprecision? -/
  moreComplexImprecise : Bool
  /-- Are they truth-conditionally equivalent (on precise reading)? -/
  truthConditionallyEquivalent : Bool
  /-- Construction type -/
  constructionType : String
  deriving Repr

/--
Plural definites: "the doors" vs "all the doors"

Source: dissertation (3), (6)
-/
def doorsAllDoors : ComplexityPrecisionPair :=
  { lessComplexExpr := "The doors are open."
  , moreComplexExpr := "All the doors are open."
  , complexitySource := "Addition of 'all'"
  , lessComplexImprecise := true   -- permits non-maximal
  , moreComplexImprecise := false  -- requires maximal
  , truthConditionallyEquivalent := true  -- on maximal reading
  , constructionType := "Plural definites"
  }

/--
Conjunctions: "Ann and Bert" vs "both Ann and Bert"

Source: dissertation (9)
-/
def andBoth : ComplexityPrecisionPair :=
  { lessComplexExpr := "Ann and Bert have red hair."
  , moreComplexExpr := "Both Ann and Bert have red hair."
  , complexitySource := "Addition of 'both'"
  , lessComplexImprecise := true   -- has homogeneity gap
  , moreComplexImprecise := false  -- gap-less
  , truthConditionallyEquivalent := true
  , constructionType := "Conjunctions"
  }

/--
Numerals: "100 cars" vs "exactly 100 cars"

Source: dissertation (4), (7)
-/
def numeralExactly : ComplexityPrecisionPair :=
  { lessComplexExpr := "Ann owns 100 cars."
  , moreComplexExpr := "Ann owns exactly 100 cars."
  , complexitySource := "Addition of 'exactly'"
  , lessComplexImprecise := true   -- permits inexact
  , moreComplexImprecise := false  -- requires exact
  , truthConditionallyEquivalent := true  -- on exact reading
  , constructionType := "Numerals"
  }

/--
Summative predicates: "blue" vs "completely blue"

Source: dissertation discussion of summative predicates
-/
def blueCompletely : ComplexityPrecisionPair :=
  { lessComplexExpr := "The flag is blue."
  , moreComplexExpr := "The flag is completely blue."
  , complexitySource := "Addition of 'completely'"
  , lessComplexImprecise := true   -- permits partial coverage
  , moreComplexImprecise := false  -- requires full coverage
  , truthConditionallyEquivalent := true
  , constructionType := "Summative predicates"
  }

-- ============================================================================
-- PART 3: Unattested Patterns
-- ============================================================================

/--
Hypothetical pattern that would violate NO NEEDLESS MANNER VIOLATIONS.
-/
structure UnattestedPattern where
  /-- The hypothetical pattern description -/
  description : String
  /-- Hypothetical less complex expression -/
  hypotheticalLessComplex : String
  /-- Hypothetical more complex expression -/
  hypotheticalMoreComplex : String
  /-- Why it's unattested (predicted by constraint) -/
  explanation : String
  /-- Closest attested analogue (if any) -/
  attestedAnalogue : Option String
  deriving Repr

/--
Hypothetical: DEF [all doors] → imprecise "the doors"

If this existed, adding DEF would add imprecision (violates constraint).

Source: dissertation (8)
-/
def defAllDoors : UnattestedPattern :=
  { description := "Morpheme DEF that adds imprecision to 'all'-QPs"
  , hypotheticalLessComplex := "[all doors] are open ≈ 'All the doors are open'"
  , hypotheticalMoreComplex := "[DEF [all doors]] are open ≈ 'The doors are open'"
  , explanation := "Adding DEF would make expression both more complex AND more imprecise. Predicted to be blocked: any alternative that is preferable on one dimension must be dispreferred on the other."
  , attestedAnalogue := none
  }

/--
Hypothetical: "approximately" that applies to non-round numerals naturally

Source: dissertation (4-c) discussion
-/
def approxNonRound : UnattestedPattern :=
  { description := "Modifier that adds imprecision to non-round numerals"
  , hypotheticalLessComplex := "Ann owns 99 cars (exact only)"
  , hypotheticalMoreComplex := "Ann owns approximately 99 cars (imprecise)"
  , explanation := "While 'approximately 99' is grammatical, it's marked/odd. Natural use of 'approximately' requires an already-round numeral. Adding complexity doesn't productively add imprecision."
  , attestedAnalogue := some "'approximately 100' (but 100 is already imprecise)"
  }

-- ============================================================================
-- PART 4: Apparent Counterexamples
-- ============================================================================

/--
Apparent counterexample that actually isn't.
-/
structure ApparentCounterexample where
  /-- The pattern -/
  pattern : String
  /-- Why it looks like a counterexample -/
  apparentProblem : String
  /-- Why it's not actually a counterexample -/
  resolution : String
  deriving Repr

/--
"every door" vs "the doors"

"every door" lacks imprecision but isn't obviously more complex.

Source: dissertation (3-c)
-/
def everyVsTheDoors : ApparentCounterexample :=
  { pattern := "'Every door is open' (precise) vs 'The doors are open' (imprecise)"
  , apparentProblem := "'Every' and 'the' seem equally simple, but differ in precision"
  , resolution := "On closer inspection: 'every' may involve covert complexity (distributivity operator, or different syntactic structure). Also, 'every' is not truth-conditionally equivalent to maximal 'the doors' (every requires non-empty domain, etc.)"
  }

/--
"approximately" with bare numerals

Adding "approximately" seems to add imprecision.

Source: dissertation (4-c)
-/
def approximatelyExample : ApparentCounterexample :=
  { pattern := "'100 cars' vs 'approximately 100 cars'"
  , apparentProblem := "'Approximately' seems to add imprecision to '100'"
  , resolution := "'100' is already imprecise - 'approximately' makes the imprecision explicit/obligatory rather than adding new imprecision. The pair isn't truth-conditionally equivalent: bare '100' CAN be exact in some contexts, 'approximately 100' cannot."
  }

-- ============================================================================
-- PART 5: Cross-Linguistic Patterns
-- ============================================================================

/--
Cross-linguistic data point for complexity-precision correlation.
-/
structure CrossLinguisticDatum where
  /-- Language -/
  language : String
  /-- Less complex form -/
  lessComplexForm : String
  /-- More complex form -/
  moreComplexForm : String
  /-- Gloss -/
  gloss : String
  /-- Does pattern hold? -/
  patternHolds : Bool
  deriving Repr

def germanDoorsExample : CrossLinguisticDatum :=
  { language := "German"
  , lessComplexForm := "Die Türen sind offen."
  , moreComplexForm := "Alle Türen sind offen."
  , gloss := "'The doors are open' vs 'All doors are open'"
  , patternHolds := true  -- same pattern as English
  }

-- ============================================================================
-- PART 6: Morphosyntactic Markedness
-- ============================================================================

/--
Markedness relation between forms.

The constraint predicts: MARKED form → MORE PRECISE meaning.

Source: Horn (1984), Krifka (2007)
-/
structure MarkednessData where
  /-- Unmarked (less marked) form -/
  unmarkedForm : String
  /-- Marked (more marked) form -/
  markedForm : String
  /-- Type of marking -/
  markingType : String
  /-- Unmarked meaning -/
  unmarkedMeaning : String
  /-- Marked meaning -/
  markedMeaning : String
  /-- Does marked = more precise? -/
  markedMorePrecise : Bool
  deriving Repr

def pluralAllMarkedness : MarkednessData :=
  { unmarkedForm := "the Ns"
  , markedForm := "all the Ns"
  , markingType := "Addition of universal quantifier"
  , unmarkedMeaning := "Universal with non-maximal option"
  , markedMeaning := "Strict universal only"
  , markedMorePrecise := true
  }

def bareNumeralMarkedness : MarkednessData :=
  { unmarkedForm := "100"
  , markedForm := "exactly 100"
  , markingType := "Addition of precision adverb"
  , unmarkedMeaning := "Exact with imprecise option"
  , markedMeaning := "Exact only"
  , markedMorePrecise := true
  }

-- ============================================================================
-- PART 7: Predictions
-- ============================================================================

/--
The NO NEEDLESS MANNER VIOLATIONS principle makes predictions.
-/
structure MannerPrediction where
  /-- Description of predicted pattern -/
  prediction : String
  /-- Is it attested? -/
  attested : Bool
  /-- Evidence -/
  evidence : String
  deriving Repr

def prediction1 : MannerPrediction :=
  { prediction := "No lexical item adds imprecision to precise base"
  , attested := true
  , evidence := "No language has DEF-like morpheme that adds homogeneity to 'all'"
  }

def prediction2 : MannerPrediction :=
  { prediction := "Precision-removing morphemes are always zero or subtract material"
  , attested := true
  , evidence := "'the doors' is simpler than 'all the doors', not vice versa"
  }

def prediction3 : MannerPrediction :=
  { prediction := "If A and B are truth-conditionally equivalent (on precise reading), and B is more complex, then B must be more precise"
  , attested := true
  , evidence := "Pattern holds for all/the, both/and, exactly/bare numerals"
  }

-- ============================================================================
-- PART 8: Key Generalizations
-- ============================================================================

/--
Core empirical generalizations about form/meaning correspondences.
-/
structure FormMeaningGeneralizations where
  /-- Less complex → more imprecision potential -/
  lessComplexMoreImprecise : Bool
  /-- Adding material → more precision -/
  addingMaterialAddsPrecision : Bool
  /-- No attested imprecision-adding morphemes -/
  noImprecisionAdders : Bool
  /-- Pattern holds cross-linguistically -/
  crossLinguistic : Bool
  /-- Pattern holds across constructions -/
  crossConstructional : Bool
  deriving Repr

def mainGeneralizations : FormMeaningGeneralizations :=
  { lessComplexMoreImprecise := true
  , addingMaterialAddsPrecision := true
  , noImprecisionAdders := true
  , crossLinguistic := true
  , crossConstructional := true
  }

-- ============================================================================
-- Collections
-- ============================================================================

def attestedPairs : List ComplexityPrecisionPair :=
  [doorsAllDoors, andBoth, numeralExactly, blueCompletely]

def unattestedPatterns : List UnattestedPattern :=
  [defAllDoors, approxNonRound]

def apparentCounterexamples : List ApparentCounterexample :=
  [everyVsTheDoors, approximatelyExample]

def predictions : List MannerPrediction :=
  [prediction1, prediction2, prediction3]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `ComplexityPrecisionPair`: Attested complexity-precision correlations
- `UnattestedPattern`: Hypothetical violations of the constraint
- `ApparentCounterexample`: Patterns that look problematic but aren't
- `CrossLinguisticDatum`: Cross-linguistic evidence
- `MarkednessData`: Morphosyntactic markedness patterns
- `MannerPrediction`: Testable predictions

### Key Finding: NO NEEDLESS MANNER VIOLATIONS
For truth-conditionally equivalent expressions φ and ψ:
- If ψ is more complex than φ, then ψ must be more precise
- If ψ is more precise than φ, then φ must be less complex
- Violations (more complex AND more imprecise) are blocked

### Key References
- Löbner (2000), Krifka (2002, 2007)
- Horn (1984), Katzir (2007)
- Dissertation Chapter 3
-/

end Phenomena.Imprecision.FormMeaning
