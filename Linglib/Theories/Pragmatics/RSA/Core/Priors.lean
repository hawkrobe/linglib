import Mathlib.Data.Real.Basic

/-!
# RSA Prior Combinators

Reusable combinators for constructing priors over product spaces and uniform
distributions. These are common building blocks for RSA models where the
world space is a product (e.g., `State × Goal` in Kao et al. 2014).
-/

set_option autoImplicit false

namespace RSA.Priors

/-- Joint prior: P(a,b) = marginal(a) * conditional(a, b). -/
def jointPrior {A B : Type*} (marginal : A → ℝ) (conditional : A → B → ℝ) :
    A × B → ℝ := fun ⟨a, b⟩ => marginal a * conditional a b

theorem jointPrior_nonneg {A B : Type*}
    {marginal : A → ℝ} {conditional : A → B → ℝ}
    (hm : ∀ a, 0 ≤ marginal a) (hc : ∀ a b, 0 ≤ conditional a b) :
    ∀ p : A × B, 0 ≤ jointPrior marginal conditional p :=
  fun ⟨a, b⟩ => mul_nonneg (hm a) (hc a b)

/-- Uniform prior: weight 1 everywhere. -/
def uniformPrior {A : Type*} : A → ℝ := fun _ => 1

theorem uniformPrior_nonneg {A : Type*} : ∀ a : A, 0 ≤ (uniformPrior a : ℝ) :=
  fun _ => le_of_lt one_pos

end RSA.Priors
