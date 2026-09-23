module

public import Linglib.Processing.DiscriminativeLexicon.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# The discriminative lexicon in normed spaces

This file proves that the production map of a discriminative lexicon over finite-dimensional
real normed spaces is Lipschitz.

Over such spaces the production map is continuous, hence Lipschitz with constant its operator
norm, so meanings within `ε` of each other produce forms within `‖production‖ * ε` of each
other. This is the quantitative form of the form–meaning isomorphy that Chuang, Bell, Tseng and
Baayen and Lu, Chuang and Baayen claim for tonal realization.

## Main results

* `Linear.lipschitzWith_production`: the production map is Lipschitz with constant its operator
  norm.
* `Linear.norm_production_sub_le`: the resulting bound on the forms of two meanings.

## References

* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal realizations
  in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [Y. Lu, Y.-Y. Chuang and R. H. Baayen, *The realization of tones in spontaneous spoken
  Taiwan Mandarin* (2026)][lu-chuang-baayen-2026]
-/

@[expose] public section

namespace DiscriminativeLexicon.Linear

variable {F M : Type*} [NormedAddCommGroup F] [NormedAddCommGroup M] [NormedSpace ℝ F]
  [NormedSpace ℝ M] [FiniteDimensional ℝ M] (D : Linear ℝ F M)

/-- The production map is Lipschitz with constant its operator norm. -/
theorem lipschitzWith_production :
    LipschitzWith ‖D.production.toContinuousLinearMap‖₊ D.production :=
  D.production.toContinuousLinearMap.lipschitzWith

/-- Meanings within `ε` of each other produce forms within `‖production‖ * ε`. -/
theorem norm_production_sub_le {e₁ e₂ : M} {ε : ℝ} (h : ‖e₁ - e₂‖ ≤ ε) :
    ‖D.production e₁ - D.production e₂‖ ≤ ‖D.production.toContinuousLinearMap‖ * ε := by
  rw [← dist_eq_norm] at h ⊢
  exact (D.lipschitzWith_production.dist_le_mul e₁ e₂).trans
    (mul_le_mul_of_nonneg_left h (norm_nonneg _))

end DiscriminativeLexicon.Linear
