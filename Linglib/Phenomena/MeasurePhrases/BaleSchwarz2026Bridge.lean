import Linglib.Core.Empirical
import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic
import Linglib.Fragments.English.MeasurePhrases

/-!
# Bale & Schwarz (2026) — Natural Language and External Conventions: Re-examining *per*

Linguistics and Philosophy 49: 133--151

## Key Claims

1. **No Division Hypothesis**: Quantity division is not available as an operation
   for semantic composition. Natural language grammar can compose quantities via
   addition and multiplication, but not division.

2. **Dual interpretation of *per*-phrases**: When *per*-phrases describe quantities
   in simplex dimensions (weight, distance), they receive compositional interpretations
   within the grammar. When they describe quantities in quotient dimensions (density,
   speed), they are instances of **math speak** --- verbalizations of quantity calculus
   notation whose meanings come from extra-grammatical conventions.

3. **Multiplication-only reformulation**: Both Coppock's (2022) and Bale & Schwarz's
   (2022) lexical entries for *per* can be restated using only pure numbers and
   multiplication, without any appeal to division.

4. **Mixed quotation parallel**: Non-compositional *per*-phrases are unified with
   mixed quotation (Davidson 1979) --- expressions that simultaneously convey
   propositional content and quote an external symbolic system.

## Diagnostics

Two tests distinguish compositional from non-compositional *per*-phrases:

- **Substitution**: Replacing unit nouns with nonsense verbalizations of the
  quantity calculus symbols (*gee over em el* for g/mL) preserves meaning for
  quotient uses but not simplex uses.

- **Sub-extraction / movement**: Fronting *per milliliter* is grammatical for
  simplex uses ("Per milliliter, this sample weighs thirteen grams") but
  blocked for quotient uses ("#Per milliliter, the density of that sample
  is thirteen grams"), because math speak lacks internal syntactic structure.

## References

- Bale, A. & Schwarz, B. (2026). Natural language and external conventions:
  re-examining *per*. *Linguistics and Philosophy* 49, 133--151.
- Bale, A. & Schwarz, B. (2022). Measurements from "per" without complex
  dimensions. *SALT 32*, 543--560.
- Coppock, E. (2022). Division vs. distributivity: Is *per* just like *each*?
  *SALT 32*, 384--403.
- Davidson, D. (1979). Quotation. *Theory and Decision* 11(1), 27--40.
-/

namespace Phenomena.MeasurePhrases.BaleSchwarz2026

open Phenomena
open TruthConditional.Measurement (Dimension QuotientDimension DimensionType)
open Fragments.English.MeasurePhrases (PerInterpretation)

-- ============================================================================
-- Section 2: Per-Phrase Classification
-- ============================================================================

/-- A *per*-phrase example with its classification. -/
structure PerPhraseExample where
  /-- The surface string (e.g., "thirteen grams per milliliter"). -/
  surface : String
  /-- The quantity argument (e.g., "thirteen grams"). -/
  quantityArg : String
  /-- The unit in the denominator (e.g., "milliliter"). -/
  perUnit : String
  /-- What dimension the phrase describes. -/
  dimType : DimensionType
  /-- How the phrase gets its meaning. -/
  source : PerInterpretation
  /-- Can the *per*-phrase be sub-extracted / fronted? -/
  allowsSubExtraction : Bool
  /-- Can unit nouns be replaced by nonsense verbalizations? -/
  allowsSubstitution : Bool
  deriving Repr, BEq

-- ============================================================================
-- Section 3: Core Examples from the Paper
-- ============================================================================

-- Simplex-dimension uses: compositional, allow sub-extraction, block substitution

/-- (8-a) "This sample of liquid weighs thirteen grams per milliliter."
Measure predicate *weighs* selects for weight (simplex). The *per*-phrase
describes a quantity of weight, not density. -/
def ex8a : PerPhraseExample where
  surface := "This sample of liquid weighs thirteen grams per milliliter"
  quantityArg := "thirteen grams"
  perUnit := "milliliter"
  dimType := .simplex
  source := .compositional
  allowsSubExtraction := true
  allowsSubstitution := false

/-- (8-b) "The train covered thirty miles per hour."
Measure predicate *covered* selects for distance (simplex). -/
def ex8b : PerPhraseExample where
  surface := "During its six-hour trip, the train covered thirty miles per hour"
  quantityArg := "thirty miles"
  perUnit := "hour"
  dimType := .simplex
  source := .compositional
  allowsSubExtraction := true
  allowsSubstitution := false

-- Quotient-dimension uses: math speak, block sub-extraction, allow substitution

/-- (6-a) "The density of that sample of liquid is thirteen grams per milliliter."
The predicate *density* selects for a quotient dimension. The *per*-phrase
verbalizes the quantity calculus expression '13 g/mL'. -/
def ex6a : PerPhraseExample where
  surface := "The density of that sample of liquid is thirteen grams per milliliter"
  quantityArg := "thirteen grams"
  perUnit := "milliliter"
  dimType := .quotient
  source := .mathSpeak
  allowsSubExtraction := false
  allowsSubstitution := true

/-- (6-b) "The speed of that train is thirty miles per hour." -/
def ex6b : PerPhraseExample where
  surface := "The speed of that train is thirty miles per hour"
  quantityArg := "thirty miles"
  perUnit := "hour"
  dimType := .quotient
  source := .mathSpeak
  allowsSubExtraction := false
  allowsSubstitution := true

-- Idiomatic uses: non-compositional, idiomatic unit

/-- (22) "The air pressure in this tire is 33 pounds per square inch."
*Pounds per square inch* is an idiom (speakers know it as *psi*
without knowing what a pound-force per square inch is). -/
def ex22 : PerPhraseExample where
  surface := "The air pressure in this tire is 33 pounds per square inch"
  quantityArg := "33 pounds"
  perUnit := "square inch"
  dimType := .quotient
  source := .idiomatic
  allowsSubExtraction := false
  allowsSubstitution := true

-- ============================================================================
-- Section 4: Substitution Diagnostic
-- ============================================================================

/-- Substitution test: replacing unit nouns with math-speak verbalizations.

(25-a) "thirteen gee over em el" verbalizes '13 g/mL'
(25-b) "thirty em pee aitch" verbalizes '30 mph'

These substitutions preserve meaning for quotient uses (math speak)
but produce nonsense for simplex uses. -/
structure SubstitutionTest where
  /-- Original phrase. -/
  original : String
  /-- Substituted phrase (with nonsense verbalizations). -/
  substituted : String
  /-- Does the substituted phrase preserve the original meaning? -/
  meaningPreserved : Bool
  deriving Repr, BEq

def subst_density : SubstitutionTest where
  original := "The density of that sample is thirteen grams per milliliter"
  substituted := "The density of that sample is thirteen gee over em el"
  meaningPreserved := true

def subst_weight : SubstitutionTest where
  original := "This sample weighs thirteen grams per milliliter"
  substituted := "This sample weighs thirteen gee over em el"
  meaningPreserved := false

-- ============================================================================
-- Section 5: Sub-Extraction Diagnostic
-- ============================================================================

/-- Sub-extraction test: can the *per*-PP be fronted?

Compositional *per*-phrases have internal syntactic structure and allow
movement. Math-speak *per*-phrases lack internal structure (like mixed
quotations) and block sub-extraction. -/
structure SubExtractionTest where
  /-- Base sentence. -/
  base : String
  /-- Fronted version. -/
  fronted : String
  /-- Is the fronted version grammatical? -/
  grammatical : Bool
  deriving Repr, BEq

/-- (29) Simplex: sub-extraction OK. -/
def extract_weight : SubExtractionTest where
  base := "This sample of liquid weighs thirteen grams per milliliter"
  fronted := "Per milliliter, this sample of liquid weighs thirteen grams"
  grammatical := true

/-- (27) Quotient: sub-extraction blocked. -/
def extract_density : SubExtractionTest where
  base := "The density of that sample is thirteen grams per milliliter"
  fronted := "Per milliliter, the density of that sample is thirteen grams"
  grammatical := false

/-- (30) Simplex: sub-extraction OK. -/
def extract_distance : SubExtractionTest where
  base := "The train covered thirty miles per hour"
  fronted := "Per hour, the train covered thirty miles"
  grammatical := true

/-- (28) Quotient: sub-extraction blocked. -/
def extract_speed : SubExtractionTest where
  base := "The speed of that train is thirty miles per hour"
  fronted := "Per hour, the speed of that train is thirty miles"
  grammatical := false

-- ============================================================================
-- Section 6: Verification Theorems
-- ============================================================================

/-- Simplex *per*-phrases allow sub-extraction. -/
theorem simplex_allows_extraction :
    ex8a.allowsSubExtraction = true ∧ ex8b.allowsSubExtraction = true := ⟨rfl, rfl⟩

/-- Quotient *per*-phrases block sub-extraction. -/
theorem quotient_blocks_extraction :
    ex6a.allowsSubExtraction = false ∧ ex6b.allowsSubExtraction = false := ⟨rfl, rfl⟩

/-- Substitution is possible for math speak, not for compositional uses. -/
theorem substitution_diagnostic :
    subst_density.meaningPreserved = true ∧
    subst_weight.meaningPreserved = false := ⟨rfl, rfl⟩

/-- The two diagnostics align: sub-extraction and substitution give opposite results.
Compositional uses: sub-extraction OK, substitution fails.
Math speak uses: sub-extraction fails, substitution OK. -/
theorem diagnostics_align :
    (ex8a.allowsSubExtraction = true ∧ ex8a.allowsSubstitution = false) ∧
    (ex6a.allowsSubExtraction = false ∧ ex6a.allowsSubstitution = true) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ============================================================================
-- Section 7: Diagnostic Prediction from Dimension Type
-- ============================================================================

/-- The Bale & Schwarz generalization: dimension type determines diagnostics.

For any *per*-phrase example, if it describes a simplex dimension then it
allows sub-extraction and blocks substitution; if it describes a quotient
dimension then it blocks sub-extraction and allows substitution.

This is a DERIVED prediction, not a stipulation: we prove it holds for ALL
examples in our data, so adding a new example that violates the pattern
would break the theorem. -/

def allExamples : List PerPhraseExample := [ex8a, ex8b, ex6a, ex6b, ex22]

/-- Every simplex-dimension example allows sub-extraction. -/
theorem simplex_predicts_extraction :
    ∀ ex ∈ allExamples, ex.dimType = .simplex → ex.allowsSubExtraction = true := by
  simp [allExamples]; decide

/-- Every quotient-dimension example blocks sub-extraction. -/
theorem quotient_predicts_no_extraction :
    ∀ ex ∈ allExamples, ex.dimType = .quotient → ex.allowsSubExtraction = false := by
  simp [allExamples]; decide

/-- Every simplex-dimension example blocks substitution. -/
theorem simplex_predicts_no_substitution :
    ∀ ex ∈ allExamples, ex.dimType = .simplex → ex.allowsSubstitution = false := by
  simp [allExamples]; decide

/-- Every quotient-dimension example allows substitution. -/
theorem quotient_predicts_substitution :
    ∀ ex ∈ allExamples, ex.dimType = .quotient → ex.allowsSubstitution = true := by
  simp [allExamples]; decide

/-- The full biconditional: sub-extraction ↔ simplex, substitution ↔ quotient. -/
theorem diagnostic_biconditional :
    ∀ ex ∈ allExamples,
      (ex.allowsSubExtraction = true ↔ ex.dimType = .simplex) ∧
      (ex.allowsSubstitution = true ↔ ex.dimType = .quotient) := by
  simp [allExamples]; decide

end Phenomena.MeasurePhrases.BaleSchwarz2026
