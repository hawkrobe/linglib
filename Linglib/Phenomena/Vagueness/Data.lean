/-
# Vagueness: Empirical Data and Theoretical Puzzles

Theory-neutral empirical patterns and formal puzzles for vague predicates.

## Scope

This module covers vagueness-specific phenomena:
- **Borderline Cases**: Intermediate judgments for middle values
- **Sorites Paradox**: Acceptance of individual premises, rejection of conclusion
- **Higher-Order Vagueness**: Borderline cases of borderline cases
- **Penumbral Connections**: Logical relationships in borderline region
- **Tolerance Principle**: The key sorites ingredient

For degree semantics (scale structure, Kennedy typology, degree modifiers),
see `Phenomena/Degrees.lean`.

## Key Insight

Vagueness arises from degree semantics + threshold uncertainty:
- Degrees provide the underlying scale
- Uncertain thresholds create borderline cases and sorites susceptibility

## Key References

- Fine, K. (1975). Vagueness, truth and logic.
- Williamson, T. (1994). Vagueness.
- Edgington, D. (1997). Vagueness by degrees.
- Keefe, R. (2000). Theories of Vagueness.
- Lassiter, D. & Goodman, N. (2017). Adjectival vagueness in a Bayesian model.
-/

import Linglib.Phenomena.Degrees

namespace Phenomena.Vagueness

-- Re-export degree types that are useful for vagueness discussions
open Phenomena.Degrees (AdjectiveClass)

-- ============================================================================
-- PART 1: Borderline Cases Data
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

/-- House price borderline example. -/
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

/-- Height borderline example. -/
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

def borderlineExamples : List BorderlineDatum :=
  [expensiveHouse, tallPerson]

-- ============================================================================
-- PART 2: Sorites Paradox Data
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
  adjective : String
  scale : String
  toleranceGap : String
  clearPositive : String
  positiveValue : String
  clearNegative : String
  negativeValue : String
  numSteps : Nat
  acceptPremise1 : Bool
  acceptToleranceSteps : Bool
  acceptConclusion : Bool
  deriving Repr

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

def soritesExamples : List SoritesDatum :=
  [tallSorites, heapSorites, expensiveSorites]

-- ============================================================================
-- PART 3: Higher-Order Vagueness
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
  basePredicate : String
  clearlyPositive : String
  borderline : String
  clearlyNegative : String
  sharpClearlyBorderline : Bool
  sharpBorderlineNot : Bool
  iteratesUpward : Bool
  deriving Repr

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
  predicate : String
  eliminatesBorderline : Bool
  definitelyIsVague : Bool
  borderlineDefinitely : Bool
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
-- PART 4: Penumbral Connections
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
  connectionName : String
  formalStatement : String
  alwaysTrue : Bool
  borderlineExample : String
  supervaluationismCaptures : Bool
  degreeTheoryCaptures : Bool
  deriving Repr

def excludedMiddle : PenumbralConnectionData :=
  { connectionName := "Excluded Middle"
  , formalStatement := "∀x. Tall(x) ∨ ¬Tall(x)"
  , alwaysTrue := true
  , borderlineExample := "John is 5'9\". 'John is tall or John is not tall' is TRUE"
  , supervaluationismCaptures := true   -- true on all precisifications
  , degreeTheoryCaptures := false       -- 0.5 ∨ 0.5 = 0.5 ≠ 1 (with standard ∨)
  }

def nonContradiction : PenumbralConnectionData :=
  { connectionName := "Non-Contradiction"
  , formalStatement := "∀x. ¬(Tall(x) ∧ ¬Tall(x))"
  , alwaysTrue := true
  , borderlineExample := "John is 5'9\". 'John is tall and not tall' is FALSE"
  , supervaluationismCaptures := true
  , degreeTheoryCaptures := false  -- 0.5 ∧ 0.5 = 0.5 ≠ 0
  }

def sameHeightConnection : PenumbralConnectionData :=
  { connectionName := "Same-Height Equivalence"
  , formalStatement := "∀x y. Height(x) = Height(y) → (Tall(x) ↔ Tall(y))"
  , alwaysTrue := true
  , borderlineExample := "John and Mary are both 5'9\". 'John is tall iff Mary is tall' is TRUE"
  , supervaluationismCaptures := true  -- all precisifications respect this
  , degreeTheoryCaptures := true       -- same degree → same truth value
  }

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
-- PART 5: Tolerance Principle and Sorites
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
  predicate : String
  scale : String
  toleranceMargin : String
  individualStepAcceptable : Bool
  iterationAbsurd : Bool
  proposedResolution : String
  deriving Repr

def heightTolerance : TolerancePrincipleData :=
  { predicate := "tall"
  , scale := "height"
  , toleranceMargin := "1 mm"
  , individualStepAcceptable := true
  , iterationAbsurd := true
  , proposedResolution := "Various: epistemicism, degree theory, supervaluationism, contextualism"
  }

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
  predicate : String
  singleStepProbability : Float
  numSteps : Nat
  cumulativeProbability : Float
  premise1Accepted : Bool
  eachStepAccepted : Bool
  fullArgumentAccepted : Bool
  deriving Repr

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
-- PART 6: Theoretical Positions
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
  deriving Repr, DecidableEq, BEq

/--
Data characterizing what each theory says about key phenomena.

This allows us to track which theories predict which patterns.

Source: Keefe (2000)
-/
structure TheoryPredictionProfile where
  theory : VaguenessTheoryType
  hasSharpBoundaries : Bool
  preservesClassicalLogic : Bool
  allowsTruthValueGaps : Bool
  allowsDegreesOfTruth : Bool
  soritesResolution : String
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
-- PART 7: Formal Constraints Any Theory Must Satisfy
-- ============================================================================

/--
Formal constraints that any adequate theory of vagueness should satisfy.

These are theory-neutral desiderata. A theory's success is measured
by how well it accounts for these patterns.

Source: Various (Keefe 2000, Williamson 1994, Lassiter 2017)
-/
structure VaguenessDesideratum where
  name : String
  description : String
  formalStatement : String
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

def higherOrderProblem : VaguenessDesideratum :=
  { name := "Higher-Order Vagueness"
  , description := "The boundary of borderline cases is itself vague"
  , formalStatement := "∃x. ¬Det(Borderline(P, x)) ∧ ¬Det(¬Borderline(P, x))"
  , importance := "Sharp boundaries for borderline ≈ sharp boundaries for P"
  }

def desiderata : List VaguenessDesideratum :=
  [borderlineCasesExist, toleranceIntuition, soritesParadoxicality,
   penumbralPreservation, higherOrderProblem]

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Vagueness-Specific Phenomena

**Borderline Cases**
- `BorderlineDatum`: Structure for borderline case data
- Examples: expensive house, tall person

**Sorites Paradox**
- `SoritesDatum`: Structure for sorites arguments
- Examples: tall, heap, expensive sorites
- `ProbabilisticSoritesData`: Edgington's probabilistic dissolution

**Higher-Order Vagueness**
- `HigherOrderVaguenessData`: Borderline of borderline problem
- `DefinitelyOperatorData`: "Definitely" operator and iteration

**Penumbral Connections**
- `PenumbralConnectionData`: Classical logic in borderline region
- Examples: excluded middle, non-contradiction, same-height

**Tolerance Principle**
- `TolerancePrincipleData`: The key sorites ingredient

**Theoretical Landscape**
- `VaguenessTheoryType`: Epistemicism, supervaluationism, etc.
- `TheoryPredictionProfile`: What each theory predicts
- `VaguenessDesideratum`: Theory-neutral constraints

### Relationship to Degrees

This module imports `Phenomena.Degrees` for:
- `AdjectiveClass` (RGA vs AGA) - relevant to which adjectives are vague in which ways
- Scale structure informs which predicates have borderline cases

The key insight: **Vagueness = Degrees + Threshold Uncertainty**
- Degrees provide the underlying scale structure
- Uncertainty about thresholds creates borderline cases
- Tolerance comes from small threshold differences being unlikely
-/

end Phenomena.Vagueness
