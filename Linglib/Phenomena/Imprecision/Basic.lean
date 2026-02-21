/-
# Imprecision & Homogeneity: Empirical Phenomena

This module collects theory-neutral empirical patterns for imprecision and
homogeneity in natural language, based primarily on:

**Nina Haslinger (2024?). "Pragmatic Constraints on Imprecision."**
Doctoral Dissertation, [Institution TBD].

## Acknowledgment

The data structures and empirical generalizations in this module are drawn
from Nina Haslinger's dissertation, which provides a comprehensive treatment
of imprecision phenomena across plural definites, numerals, conjunctions,
and degree expressions. Her work identifies two key pragmatic constraints:

1. **NO NEEDLESS MANNER VIOLATIONS**: A tradeoff between structural complexity
   and semantic precision—more complex expressions must be more precise.

2. **INFERENCE PRESERVATION**: Imprecise construals must preserve inferential
   relations with alternatives that hold on the precise construal.

We are deeply grateful for her thorough empirical documentation of these
phenomena, which makes formalization possible.

## Module Structure

- `Numerals.lean`: Round vs non-round numeral imprecision
- `FormMeaning.lean`: Complexity-precision correspondences
- `Projection.lean`: How homogeneity/imprecision projects under quantifiers
- `InferencePreservation.lean`: Blocking conditions for imprecision

## Theoretical Status

These modules document **empirical phenomena only**. The theoretical machinery
required to derive predictions from the constraints (trivalent semantics,
parameter vectors, exhaustification operators, etc.) is left as future work.
See `ROADMAP.md` for the formalization plan.

## Key References

### Primary Source
- Haslinger, N. (2024?). Pragmatic Constraints on Imprecision. Doctoral Dissertation.

### Background on Homogeneity
- Löbner, S. (2000). Polarity in natural language. *Linguistics and Philosophy*.
- Križ, M. (2015). *Aspects of Homogeneity in the Semantics of Natural Language*.
  Doctoral Dissertation, University of Vienna.
- Križ, M. (2016). Homogeneity, non-maximality, and all.
  *Journal of Semantics* 33(3).
- Križ, M. & Chemla, E. (2015). Two methods to find truth-value gaps.
  *Linguistics and Philosophy* 38(3).
- Križ, M. & Spector, B. (2021). Interpreting plural predication.
  *Linguistics and Philosophy* 44(5).

### Background on Non-Maximality
- Krifka, M. (1996). Pragmatic strengthening in plural predications.
  *SALT* 6.
- Lasersohn, P. (1999). Pragmatic halos.
  *Language* 75(3).
- Malamud, S. (2012). The meaning of plural definites.
  *Semantics and Pragmatics* 5.
- Burnett, H. (2017). *Gradability in Natural Language*. Oxford University Press.

### Background on Numeral Imprecision
- Krifka, M. (2007). Approximate interpretation of number words.
  In *Cognitive Foundations of Interpretation*.
- Sauerland, U. & Stateva, P. (2007). Scalar vs. epistemic vagueness.
  *SALT* 17.
- Solt, S. (2014). An alternative theory of imprecision.
  *SALT* 24.
- Solt, S. & Waldon, B. (2019). Numerals under negation.
  *Glossa* 4(1).
- Solt, S. (2023). Imprecision without homogeneity. Ms.

### Background on Implicatures and Exhaustification
- Bar-Lev, M. (2021). An implicature account of homogeneity and non-maximality.
  *Linguistics and Philosophy* 44(5).
- Bar-Lev, M. & Fox, D. (2020). Free choice, simplification, and Innocent Inclusion.
  *Natural Language Semantics* 28.
- Bassi, I., Del Pinal, G., & Sauerland, U. (2021). Presuppositional exhaustification.
  *Semantics and Pragmatics* 14.

### Experimental Work
- Augurzky, P., Franke, M., & Reinert, C. (2023). Homogeneity and non-maximality
  under quantification. *Journal of Semantics*.
- Tieu, L., Križ, M., & Chemla, E. (2019). Children's acquisition of homogeneity
  in plural definite descriptions. *Frontiers in Psychology*.

### Complexity and Alternatives
- Horn, L. (1984). Toward a new taxonomy for pragmatic inference.
  In *Meaning, Form, and Use in Context*.
- Katzir, R. (2007). Structurally-defined alternatives.
  *Linguistics and Philosophy* 30.
-/

import Linglib.Phenomena.Plurals.Homogeneity
import Linglib.Phenomena.Plurals.NonMaximality
import Linglib.Phenomena.Imprecision.Numerals
import Linglib.Phenomena.Imprecision.FormMeaning
import Linglib.Phenomena.Imprecision.Projection
import Linglib.Phenomena.Imprecision.InferencePreservation

namespace Phenomena.Imprecision

-- Re-exports for convenient access

-- From Plurals.Homogeneity
export Phenomena.Plurals.Homogeneity (
  HomogeneityDatum
  HomogeneityJudgment
  HomogeneityRemover
  HomogeneityRemovalDatum
  ConjunctionVsPluralDatum
  switchesExample
  booksExample
  conjunctionExample
)

-- From Plurals.NonMaximality
export Phenomena.Plurals.NonMaximality (
  NonMaximalityDatum
  ContextualIssue
  BankRobberyDatum
  switchesNonMaximality
)

-- From Numerals
export Numerals (
  RoundnessLevel
  NumeralImprecisionDatum
  RoundnessAsymmetryDatum
  classifyRoundness
)

-- From FormMeaning
export FormMeaning (
  ComplexityPrecisionPair
  UnattestedPattern
  attestedPairs
  unattestedPatterns
)

-- From Projection
export Projection (
  EmbeddingOperator
  ProjectionDatum
  QUDManipulationDatum
  noNotEveryAsymmetry
)

-- From InferencePreservation
export InferencePreservation (
  NumeralBlockingDatum
  ConjunctionBlockingDatum
  inferencePreservation
)

-- Summary Statistics

/--
Summary of phenomena covered in this module.
-/
structure ImprecisionPhenomenaSummary where
  /-- Number of homogeneity examples -/
  homogeneityExamples : Nat
  /-- Number of non-maximality examples -/
  nonMaximalityExamples : Nat
  /-- Number of numeral imprecision examples -/
  numeralExamples : Nat
  /-- Number of form/meaning pairs -/
  formMeaningPairs : Nat
  /-- Number of projection patterns -/
  projectionPatterns : Nat
  /-- Number of inference preservation examples -/
  inferencePreservationExamples : Nat
  deriving Repr

def phenomenaSummary : ImprecisionPhenomenaSummary :=
  { homogeneityExamples := 6  -- switches, books, conjunction, summative, conditional, collective
  , nonMaximalityExamples := 7  -- switches, bank robbery (5 configs), problem sets
  , numeralExamples := 5  -- cars (2), roundness pairs (2), game show
  , formMeaningPairs := 4  -- doors/all, and/both, 100/exactly, blue/completely
  , projectionPatterns := 3  -- every, no, not every
  , inferencePreservationExamples := 4  -- 99, 100, conjunction (2)
  }

-- Promissory Notes for Future Work

/-
## Future Work: Theoretical Infrastructure

To formalize the theoretical predictions from Haslinger's dissertation,
we will need:

### Core/Trivalent.lean
- Three-valued logic (true, false, gap)
- Strong Kleene connectives
- Gap projection mechanisms

### Core/ParameterVector.lean
- Homogeneity parameters (f^i)
- Granularity parameters (d^i)
- Alternative set functions (ALT)
- Selection functions (S_p)

### Core/StrongRelevance.lean
- Issue as partition
- Strong relevance predicate
- Partition alignment

### Core/SyntacticComplexity.lean
- Complexity measure on expressions
- Comparison relation

### Theories/Imprecision/Exhaustification.lean
- Innocent Exclusion and Inclusion
- Alternative pruning
- exh operator with gap introduction

### Theories/Imprecision/Constraints.lean
- NO NEEDLESS MANNER VIOLATIONS theorem
- INFERENCE PRESERVATION theorem
- Predictions for specific constructions

See ROADMAP.md for detailed formalization plan.
-/

end Phenomena.Imprecision
