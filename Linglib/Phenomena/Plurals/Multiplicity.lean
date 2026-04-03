import Linglib.Core.Polarity

/-!
# Multiplicity Inferences: Empirical Data

Theory-neutral empirical patterns for multiplicity inferences —
the observation that bare plurals trigger a "more than one" reading
in upward-entailing contexts but not in downward-entailing contexts.

## The Puzzle

- "Emily fed giraffes" → Emily fed more than one giraffe
- "Emily didn't feed giraffes" ≠ Emily didn't feed more than one giraffe
  (rather: Emily didn't feed any giraffes)

This monotonicity sensitivity parallels classical scalar implicatures
(e.g., "some" → "not all" in UE but not DE contexts).

## Theoretical Approaches

Three main accounts:
1. **Ambiguity** (@cite{farkas-de-swart-2010}): Plural is ambiguous
   (inclusive "one or more" vs exclusive "more than one"), resolved by
   Strongest Meaning Hypothesis.
2. **Implicature** (@cite{sauerland-2003}, @cite{spector-2007},
   @cite{zweig-2009}): Plural literally means "one or more," multiplicity
   arises as a scalar implicature with the singular as alternative.
3. **Homogeneity** (@cite{kriz-2015}): Plural interpretation via
   homogeneity presupposition.

## Key References

- @cite{sauerland-2003}
- @cite{spector-2007}
- @cite{zweig-2009}
- @cite{farkas-de-swart-2010}
- @cite{tieu-etal-2020}
-/

namespace Phenomena.Plurals.Multiplicity

open Core (Polarity)


/--
A multiplicity inference datum: a bare plural sentence tested
in upward-entailing (positive) and downward-entailing (negative) contexts.
-/
structure MultiplicityDatum where
  /-- The bare plural sentence (positive form) -/
  positiveSentence : String
  /-- The negated form -/
  negativeSentence : String
  /-- Does the "more than one" inference arise in the positive? -/
  multiplicityInPositive : Bool
  /-- Does the "more than one" inference arise in the negative? -/
  multiplicityInNegative : Bool
  deriving Repr

/--
Core example: "Emily fed giraffes."

In UE: interpreted as "Emily fed more than one giraffe."
In DE: "Emily didn't feed giraffes" ≈ "Emily didn't feed any giraffes."
-/
def fedGiraffes : MultiplicityDatum :=
  { positiveSentence := "Emily fed giraffes"
  , negativeSentence := "Emily didn't feed giraffes"
  , multiplicityInPositive := true
  , multiplicityInNegative := false
  }

/-- Conditional antecedent (DE context). -/
def booksOnDesk : MultiplicityDatum :=
  { positiveSentence := "There are books on Stephen's desk"
  , negativeSentence := "If there are books on Stephen's desk, Robin should lock the door"
  , multiplicityInPositive := true
  , multiplicityInNegative := false
  }

def allExamples : List MultiplicityDatum :=
  [fedGiraffes, booksOnDesk]

/-- Multiplicity arises in UE but not DE — the core monotonicity pattern. -/
theorem monotonicity_pattern :
    allExamples.all (λ d => d.multiplicityInPositive && !d.multiplicityInNegative) := by
  native_decide


/--
The monotonicity sensitivity of multiplicity inferences parallels that
of classical scalar implicatures. This structure captures the parallel.
-/
structure MonotonicityParallel where
  /-- The scalar term (e.g., "some", bare plural) -/
  weakTerm : String
  /-- Its stronger alternative (e.g., "all", singular) -/
  strongAlternative : String
  /-- Inference in UE context -/
  inferenceInUE : String
  /-- Does inference arise in UE? -/
  arisesInUE : Bool
  /-- Does inference arise in DE? -/
  arisesInDE : Bool
  deriving Repr

/-- Some/all parallel. -/
def someAllParallel : MonotonicityParallel :=
  { weakTerm := "some"
  , strongAlternative := "all"
  , inferenceInUE := "not all"
  , arisesInUE := true
  , arisesInDE := false
  }

/-- Plural/singular parallel. -/
def pluralSingularParallel : MonotonicityParallel :=
  { weakTerm := "plural (giraffes)"
  , strongAlternative := "singular (a giraffe)"
  , inferenceInUE := "more than one"
  , arisesInUE := true
  , arisesInDE := false
  }

/-- Or/and parallel. -/
def orAndParallel : MonotonicityParallel :=
  { weakTerm := "or"
  , strongAlternative := "and"
  , inferenceInUE := "not both"
  , arisesInUE := true
  , arisesInDE := false
  }

def allParallels : List MonotonicityParallel :=
  [someAllParallel, pluralSingularParallel, orAndParallel]

/-- All three scales show the same monotonicity pattern. -/
theorem uniform_monotonicity :
    allParallels.all (λ p => p.arisesInUE && !p.arisesInDE) := by
  native_decide


/--
Competing theoretical approaches to multiplicity inferences.
-/
inductive PluralTheory where
  /-- Plural is ambiguous; Strongest Meaning Hypothesis resolves. -/
  | ambiguity
  /-- Plural literally means "one or more"; multiplicity is implicature. -/
  | implicature
  /-- Plural interpretation via homogeneity presupposition. -/
  | homogeneity
  deriving DecidableEq, Repr, Inhabited

/--
Key predictions where the three theories diverge.
-/
structure TheoryPrediction where
  /-- The theory -/
  theory : PluralTheory
  /-- Does it predict children compute fewer multiplicity inferences? -/
  childrenComputeFewer : Bool
  /-- Does it predict multiplicity rates correlate with SI rates? -/
  multiplicityCorrelatesWithSI : Bool
  /-- Can it account for asymmetric polarity pattern in children? -/
  accountsForPolarityAsymmetry : Bool
  deriving Repr, DecidableEq

/--
Positive vs negative plural sentences in singular contexts.

In a context where only one giraffe was fed:
- "Emily fed giraffes" is literally true (one or more) but carries a false
  multiplicity implicature → intermediate status (true but misleading)
- "Emily didn't feed giraffes" is literally false → clearly false

The three theories predict:
- Ambiguity: both undefined (homogeneous gap) or both false → same status
- Homogeneity: both undefined → same status
- Implicature: positive = true with false implicature, negative = false → different
-/
structure SingularContextPrediction where
  /-- The theory -/
  theory : PluralTheory
  /-- Does positive get different status from negative? -/
  positiveNegativeDiffer : Bool
  deriving Repr, DecidableEq

def ambiguitySingularPrediction : SingularContextPrediction :=
  { theory := .ambiguity, positiveNegativeDiffer := false }

def implicatureSingularPrediction : SingularContextPrediction :=
  { theory := .implicature, positiveNegativeDiffer := true }

def homogeneitySingularPrediction : SingularContextPrediction :=
  { theory := .homogeneity, positiveNegativeDiffer := false }

def allSingularPredictions : List SingularContextPrediction :=
  [ambiguitySingularPrediction, implicatureSingularPrediction, homogeneitySingularPrediction]

/-- Only the implicature approach predicts different status for
    positive vs negative in singular contexts. -/
theorem singular_context_discriminates :
    allSingularPredictions.filter (·.positiveNegativeDiffer) =
    [implicatureSingularPrediction] := by
  native_decide

def ambiguityPrediction : TheoryPrediction :=
  { theory := .ambiguity
  , childrenComputeFewer := false  -- no clear prediction
  , multiplicityCorrelatesWithSI := false  -- different mechanisms
  , accountsForPolarityAsymmetry := false  -- challenged by data
  }

def implicaturePrediction : TheoryPrediction :=
  { theory := .implicature
  , childrenComputeFewer := true   -- same mechanism as SI
  , multiplicityCorrelatesWithSI := true   -- Uniformity Prediction
  , accountsForPolarityAsymmetry := true   -- follows from implicature theory
  }

def homogeneityPrediction : TheoryPrediction :=
  { theory := .homogeneity
  , childrenComputeFewer := false  -- no clear prediction
  , multiplicityCorrelatesWithSI := false  -- different mechanisms
  , accountsForPolarityAsymmetry := false  -- challenged by data
  }

def allPredictions : List TheoryPrediction :=
  [ambiguityPrediction, implicaturePrediction, homogeneityPrediction]

/-- Only the implicature approach predicts all three findings. -/
theorem implicature_uniquely_predicts :
    allPredictions.filter (λ p =>
      p.childrenComputeFewer && p.multiplicityCorrelatesWithSI &&
      p.accountsForPolarityAsymmetry) =
    [implicaturePrediction] := by
  native_decide

end Phenomena.Plurals.Multiplicity
