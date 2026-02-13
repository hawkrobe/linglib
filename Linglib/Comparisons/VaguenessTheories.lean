/-!
# Vagueness Theory Comparison

Theory-comparative infrastructure for vagueness: characterizes what each major
theoretical position (epistemicism, supervaluationism, degree theory, contextualism)
predicts about borderline cases, sorites, higher-order vagueness, and classical logic.

This is cross-theory comparison, not empirical data — hence lives in `Comparisons/`
rather than `Phenomena/`.

## References

- Keefe, R. (2000). Theories of Vagueness.
- Williamson, T. (1994). Vagueness.
-/

namespace Comparisons.VaguenessTheories

/--
Major theoretical positions on vagueness.

This is a theory-neutral characterization of what each position claims.

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

end Comparisons.VaguenessTheories
