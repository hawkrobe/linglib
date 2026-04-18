/-
# Bayesian Semantics: Graded Truth from Parameter Uncertainty

This module explores approaches where graded truth values **emerge** from
uncertainty over predicate parameters, rather than being stipulated directly.

## Background

Three approaches to probabilistic/graded semantics:

### 1. Stipulated Graded Values (our `GradedProposition.lean`)
- Define `P : Entity → ℚ` directly
- Compose using probabilistic operations (×, +−pq)
- Simple but ad hoc

### 2. Marginalize over Parameters
- Define Boolean semantics `P_θ : Entity → Bool`
- Put a prior over θ
- Graded truth = E_θ[P_θ(x)]
- More principled but still separate from composition

### 3. Probability Monad (Grove's PDS)
- Standard compositional semantics (CCG + λ-calculus)
- Probability as a monadic effect: `P α`
- Compiles to probabilistic programs (Stan)
- Most principled: separates semantics from inference

## This Module

We implement approach #2 as a stepping stone. It shows that graded values
can emerge from Boolean semantics + uncertainty, connecting to Lassiter &
Goodman's result: "threshold semantics + uncertainty = graded semantics".

-/

import Linglib.Theories.Semantics.Probabilistic.ParamPred
import Linglib.Core.FinitePMF
import Linglib.Core.Semantics.GradedProposition
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Semantics.Montague.BayesianSemantics

open Core.GradedProposition
open Semantics.Probabilistic.ParamPred

-- Use the canonical FinitePMF from Core
open Core

-- Example: Threshold Predicates (Lassiter & Goodman Style)

/--
A threshold predicate: "x has property P iff measure(x) > θ"

This models gradable adjectives like "tall", "expensive", etc.
-/
structure ThresholdPred (E : Type*) (Θ : Type*) [Fintype Θ] [Preorder Θ] where
  /-- The measure function (e.g., height, price) -/
  measure : E → Θ
  /-- Prior over thresholds -/
  thresholdPrior : FinitePMF Θ

namespace ThresholdPred

variable {E Θ : Type*} [Fintype Θ] [DecidableEq Θ] [Preorder Θ]
variable [DecidableRel (· < · : Θ → Θ → Prop)]

/-- Convert to a parameterized predicate -/
def toParamPred (pred : ThresholdPred E Θ) : ParamPred E Θ where
  semantics := λ θ x => pred.measure x > θ
  prior := pred.thresholdPrior

/-- Graded truth for threshold predicates -/
def gradedTruth (pred : ThresholdPred E Θ) (x : E) : ℚ :=
  pred.toParamPred.gradedTruth x

/--
Graded truth equals probability that measure > threshold.

For "tall(John)": P(height(John) > θ) under the threshold prior.
-/
theorem gradedTruth_eq_prob (pred : ThresholdPred E Θ) (x : E) :
    pred.gradedTruth x = pred.thresholdPrior.prob (λ θ => pred.measure x > θ) := rfl

end ThresholdPred

-- Feature-Based Predicates (Bernardy Style)

/--
A feature-based predicate where entities are characterized by features
and the predicate is a linear classifier.

Entity satisfaction: `bias + Σᵢ weight_i · feature_i(x) > 0`

This models the Bernardy et al. approach where predicates are hyperplanes.
-/
structure FeaturePred (E : Type*) (n : ℕ) where
  /-- Extract feature vector from entity -/
  features : E → Fin n → ℚ
  /-- Predicate parameters: bias and weights -/
  params : Type*
  /-- Fintype instance for params -/
  [paramsFintype : Fintype params]
  [paramsDecEq : DecidableEq params]
  /-- Bias for each parameter setting -/
  bias : params → ℚ
  /-- Weights for each parameter setting -/
  weights : params → Fin n → ℚ
  /-- Prior over parameters -/
  prior : FinitePMF params

attribute [instance] FeaturePred.paramsFintype FeaturePred.paramsDecEq

namespace FeaturePred

variable {E : Type*} {n : ℕ}

/-- Dot product of weight vector and feature vector -/
def dotProduct (w f : Fin n → ℚ) : ℚ :=
  Finset.sum Finset.univ λ i => w i * f i

/-- Boolean semantics for a specific parameter setting -/
def satisfies (pred : FeaturePred E n) (p : pred.params) (x : E) : Bool :=
  pred.bias p + dotProduct (pred.weights p) (pred.features x) > 0

/-- Convert to parameterized predicate -/
def toParamPred (pred : FeaturePred E n) : ParamPred E pred.params where
  semantics := pred.satisfies
  prior := pred.prior

/-- Graded truth emerges from parameter uncertainty -/
def gradedTruth (pred : FeaturePred E n) (x : E) : ℚ :=
  pred.toParamPred.gradedTruth x

end FeaturePred

-- Composition

/-!
## Compositional Structure
@cite{bernardy-blanck-chatzikyriakidis-lappin-2018}

### Two Strategies

1. **Marginalize early** (`GradedProposition.lean`):
   - Convert to graded values immediately
   - Compose using probabilistic operations (×, +−pq)
   - Algebraic structure (De Morgan, etc.)

2. **Marginalize late** (this module):
   - Keep Boolean semantics during composition
   - Parameter uncertainty tracked but not resolved
   - Graded values emerge only when needed

3. **Probability monad** (Grove's PDS):
   - Standard compositional semantics
   - Probability as monadic effect
   - Compiles to probabilistic programs

Strategy #3 is most principled but requires more infrastructure.
This module implements #2 as an intermediate step.
-/

end Semantics.Montague.BayesianSemantics
