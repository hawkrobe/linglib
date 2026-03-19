import Linglib.Core.FinitePMF
import Linglib.Core.Semantics.GradedProposition
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Parameterized Predicates
@cite{lassiter-goodman-2017} @cite{grove-white-2025}

Boolean predicates parameterized by a latent variable, with a prior over
that variable. Graded truth values **emerge** from marginalizing over the
parameter: `P(x) = E_θ[P_θ(x)]`.

This pattern applies whenever gradience arises from uncertainty over a
discrete parameter:
- **Gradable adjectives**: θ = threshold, `⟦tall⟧_θ(x) = height(x) > θ`
- **Factivity**: θ ∈ {factive, nonfactive}, `⟦know⟧_factive = BEL ∧ C`
- **Generics**: θ = prevalence threshold
- **Polysemy**: θ indexes word senses

The key theorem `gradedTruth_pure` shows that a point-mass prior (no
uncertainty) recovers Boolean truth — gradience is not stipulated but
emerges from parameter uncertainty.
-/

namespace Semantics.Probabilistic.ParamPred

open Core.GradedProposition
open Core

/--
A parameterized predicate has:
- A parameter space Θ
- For each θ, a Boolean predicate on entities
- A prior distribution over Θ

The graded truth value emerges from marginalizing over Θ.
-/
structure ParamPred (E Θ : Type*) [Fintype Θ] where
  semantics : Θ → E → Bool
  prior : FinitePMF Θ

namespace ParamPred

variable {E Θ : Type*} [Fintype Θ] [DecidableEq Θ]

/-- Graded truth value: `P(x) = E_θ[P_θ(x)]`. -/
def gradedTruth (pred : ParamPred E Θ) (x : E) : ℚ :=
  pred.prior.prob λ θ => pred.semantics θ x

/-- Convert a parameterized predicate to a graded predicate. -/
def toGPred (pred : ParamPred E Θ) : GPred E :=
  pred.gradedTruth

/-- For a point mass prior (no uncertainty), graded truth = Boolean truth. -/
theorem gradedTruth_pure (sem : Θ → E → Bool) (θ₀ : Θ) (x : E) :
    (ParamPred.mk sem (FinitePMF.pure θ₀)).gradedTruth x =
    if sem θ₀ x then 1 else 0 := by
  simp only [gradedTruth, FinitePMF.prob, FinitePMF.expect_pure]

/-- Graded truth unfolds to expected value of the Boolean indicator. -/
theorem gradedTruth_eq_expect (sem : Θ → E → Bool) (prior : FinitePMF Θ) (x : E) :
    (ParamPred.mk sem prior).gradedTruth x =
    prior.expect (λ θ => if sem θ x then 1 else 0) := rfl

end ParamPred

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

end Semantics.Probabilistic.ParamPred
