import Linglib.Theories.Semantics.Probabilistic.ParamPred
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Bayesian Semantics: Graded Truth from Parameter Uncertainty

This module explores approaches where graded truth values **emerge** from
uncertainty over predicate parameters, rather than being stipulated directly.

## Background

Three approaches to probabilistic/graded semantics:

### 1. Stipulated Graded Values
- Define `P : Entity → ℝ≥0∞` directly
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

Priors are mathlib `PMF`-valued (`ℝ≥0∞`), matching the rest of the
probability layer.
-/

set_option autoImplicit false

namespace Semantics.Montague.BayesianSemantics

open Semantics.Probabilistic
open scoped ENNReal

-- Example: Threshold Predicates (Lassiter & Goodman Style)

/--
A threshold predicate: "x has property P iff measure(x) > θ"

This models gradable adjectives like "tall", "expensive", etc.
-/
structure ThresholdPred (E : Type*) (Θ : Type*) [Fintype Θ] [Preorder Θ] where
  /-- The measure function (e.g., height, price) -/
  measure : E → Θ
  /-- Prior over thresholds -/
  thresholdPrior : PMF Θ

namespace ThresholdPred

variable {E Θ : Type*} [Fintype Θ] [Preorder Θ]
variable [DecidableRel (· < · : Θ → Θ → Prop)]

/-- Convert to a parameterized predicate -/
def toParamPred (pred : ThresholdPred E Θ) : ParamPred E Θ where
  semantics := λ θ x => pred.measure x > θ
  prior := pred.thresholdPrior

/-- Graded truth for threshold predicates -/
noncomputable def gradedTruth (pred : ThresholdPred E Θ) (x : E) : ℝ≥0∞ :=
  pred.toParamPred.gradedTruth x

/--
Graded truth equals probability that measure > threshold.

For "tall(John)": P(height(John) > θ) under the threshold prior.
-/
theorem gradedTruth_eq_probOfSet (pred : ThresholdPred E Θ) (x : E) :
    pred.gradedTruth x =
      pred.thresholdPrior.probOfSet {θ | pred.measure x > θ} := by
  show pred.thresholdPrior.probOfSet {θ | decide (pred.measure x > θ) = true} = _
  congr 1
  ext θ
  simp

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
  prior : PMF params

attribute [instance] FeaturePred.paramsFintype FeaturePred.paramsDecEq

namespace FeaturePred

variable {E : Type*} {n : ℕ}

/-- Boolean semantics for a specific parameter setting: the linear classifier
`bias + Σᵢ weight_i · feature_i(x) > 0`. -/
def satisfies (pred : FeaturePred E n) (p : pred.params) (x : E) : Bool :=
  pred.bias p + ∑ i, pred.weights p i * pred.features x i > 0

/-- Convert to parameterized predicate -/
def toParamPred (pred : FeaturePred E n) : ParamPred E pred.params where
  semantics := pred.satisfies
  prior := pred.prior

/-- Graded truth emerges from parameter uncertainty -/
noncomputable def gradedTruth (pred : FeaturePred E n) (x : E) : ℝ≥0∞ :=
  pred.toParamPred.gradedTruth x

end FeaturePred

-- Composition

/-!
## Compositional Structure
@cite{bernardy-blanck-chatzikyriakidis-lappin-2018}

### Two Strategies

1. **Marginalize early**:
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
