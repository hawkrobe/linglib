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

### 2. Marginalize over Parameters (Bernardy et al. 2018)
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

## References

- Bernardy et al. (2018). A Compositional Bayesian Semantics for Natural Language.
- Grove & White. Probabilistic Dynamic Semantics.
- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
-/

import Linglib.Core.Proposition
import Linglib.Theories.Montague.GradedProposition
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Theories.Montague.BayesianSemantics

open Core.Proposition
open Core.GradedProposition

-- Finite PMF (Simple Version)

/--
A finite probability mass function over type Θ.

This is a simplified PMF for finite types using rationals.
Values are non-negative and sum to 1.

For full Mathlib PMF integration with ℝ≥0∞, see:
`Mathlib.Probability.ProbabilityMassFunction.Basic`
-/
structure FinitePMF (Θ : Type*) [Fintype Θ] where
  /-- Probability mass function -/
  mass : Θ → ℚ
  /-- All masses are non-negative -/
  mass_nonneg : ∀ θ, 0 ≤ mass θ := by intros; decide
  /-- Masses sum to 1 -/
  mass_sum_one : Finset.sum Finset.univ mass = 1 := by native_decide

namespace FinitePMF

variable {Θ : Type*} [Fintype Θ] [DecidableEq Θ]

/-- Point mass at a single value -/
def pure (θ₀ : Θ) : FinitePMF Θ where
  mass := λ θ => if θ = θ₀ then 1 else 0
  mass_nonneg := λ θ => by split_ifs <;> decide
  mass_sum_one := by
    rw [Finset.sum_eq_single θ₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact (h (Finset.mem_univ _)).elim

/-- Expected value of a function under this distribution -/
def expect (pmf : FinitePMF Θ) (f : Θ → ℚ) : ℚ :=
  Finset.sum Finset.univ λ θ => pmf.mass θ * f θ

/-- Expected value of an indicator (probability of event) -/
def prob (pmf : FinitePMF Θ) (event : Θ → Bool) : ℚ :=
  pmf.expect λ θ => if event θ then 1 else 0

/-- Expected value of pure distribution is the value at that point -/
theorem expect_pure (θ₀ : Θ) (f : Θ → ℚ) :
    (pure θ₀).expect f = f θ₀ := by
  simp only [expect, pure]
  rw [Finset.sum_eq_single θ₀]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact (h (Finset.mem_univ _)).elim

end FinitePMF

-- Parameterized Predicates

/--
A parameterized predicate has:
- A parameter space Θ
- For each θ, a Boolean predicate on entities

The graded truth value emerges from marginalizing over Θ.
-/
structure ParamPred (E Θ : Type*) [Fintype Θ] where
  /-- Boolean semantics given a parameter value -/
  semantics : Θ → E → Bool
  /-- Prior distribution over parameters -/
  prior : FinitePMF Θ

namespace ParamPred

variable {E Θ : Type*} [Fintype Θ] [DecidableEq Θ]

/--
Graded truth value: expected value of the Boolean predicate.

`P(x) = E_θ[P_θ(x)]`
-/
def gradedTruth (pred : ParamPred E Θ) (x : E) : ℚ :=
  pred.prior.prob λ θ => pred.semantics θ x

/--
Convert a parameterized predicate to a graded predicate.

This is how graded truth values *emerge* from Boolean semantics
+ parameter uncertainty.
-/
def toGPred (pred : ParamPred E Θ) : GPred E :=
  pred.gradedTruth

/--
For a point mass prior (no uncertainty), graded truth = Boolean truth.
-/
theorem gradedTruth_pure (sem : Θ → E → Bool) (θ₀ : Θ) (x : E) :
    (ParamPred.mk sem (FinitePMF.pure θ₀)).gradedTruth x =
    if sem θ₀ x then 1 else 0 := by
  simp only [gradedTruth, FinitePMF.prob, FinitePMF.expect_pure]

/-- Graded truth unfolds to expected value of the Boolean indicator. -/
theorem gradedTruth_eq_expect (sem : Θ → E → Bool) (prior : FinitePMF Θ) (x : E) :
    (ParamPred.mk sem prior).gradedTruth x =
    prior.expect (λ θ => if sem θ x then 1 else 0) := rfl

end ParamPred

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

/--
Compose two parameterized predicates via conjunction.

The result has uncertainty over both parameters (product space).
Under independence, the joint prior is the product of individual priors.
-/
def ParamPred.conj {E Θ₁ Θ₂ : Type*}
    [Fintype Θ₁] [Fintype Θ₂] [DecidableEq Θ₁] [DecidableEq Θ₂]
    (p : ParamPred E Θ₁) (q : ParamPred E Θ₂) : ParamPred E (Θ₁ × Θ₂) where
  semantics := λ ⟨θ₁, θ₂⟩ x => p.semantics θ₁ x && q.semantics θ₂ x
  prior := {
    mass := λ ⟨θ₁, θ₂⟩ => p.prior.mass θ₁ * q.prior.mass θ₂
    mass_nonneg := λ ⟨θ₁, θ₂⟩ => mul_nonneg (p.prior.mass_nonneg θ₁) (q.prior.mass_nonneg θ₂)
    mass_sum_one := by
      simp only [Fintype.sum_prod_type]
      calc Finset.sum Finset.univ (λ a =>
             Finset.sum Finset.univ (λ b => p.prior.mass a * q.prior.mass b))
          = Finset.sum Finset.univ (λ a =>
              p.prior.mass a * Finset.sum Finset.univ q.prior.mass) := by
            congr 1; ext a; rw [← Finset.mul_sum]
        _ = Finset.sum Finset.univ (λ a => p.prior.mass a * 1) := by
            rw [q.prior.mass_sum_one]
        _ = 1 := by simp [p.prior.mass_sum_one]
  }

end Theories.Montague.BayesianSemantics
