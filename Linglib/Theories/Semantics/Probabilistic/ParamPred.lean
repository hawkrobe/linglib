import Linglib.Core.Probability.PMFFin

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

set_option autoImplicit false

namespace Semantics.Probabilistic

open scoped ENNReal

/--
A parameterized predicate has:
- A parameter space Θ
- For each θ, a Boolean predicate on entities
- A prior distribution over Θ (mathlib `PMF`, `ℝ≥0∞`-valued)

The graded truth value emerges from marginalizing over Θ.
-/
structure ParamPred (E Θ : Type*) [Fintype Θ] where
  semantics : Θ → E → Bool
  prior : PMF Θ

namespace ParamPred

variable {E Θ : Type*} [Fintype Θ]

/-- Graded truth value: `P(x) = prior {θ | semantics θ x}`. The prior's
mass on the set of parameter values where the Boolean predicate holds. -/
noncomputable def gradedTruth (pred : ParamPred E Θ) (x : E) : ℝ≥0∞ :=
  pred.prior.probOfSet {θ | pred.semantics θ x = true}

/-- For a point-mass prior (no uncertainty), graded truth = Boolean truth.
The substantive theorem: gradience emerges from parameter uncertainty,
not from the predicate itself. -/
theorem gradedTruth_pure (sem : Θ → E → Bool) (θ₀ : Θ) (x : E) :
    (ParamPred.mk sem (PMF.pure θ₀)).gradedTruth x =
    if sem θ₀ x then 1 else 0 := by
  show (PMF.pure θ₀).toOuterMeasure {θ | sem θ x = true} = _
  rw [PMF.toOuterMeasure_pure_apply]
  simp [Set.mem_setOf_eq]

end ParamPred

end Semantics.Probabilistic
