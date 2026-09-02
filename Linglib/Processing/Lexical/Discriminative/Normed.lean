import Linglib.Processing.Lexical.Discriminative.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# DLM in normed carriers

Over finite-dimensional real normed carriers the production map is continuous, hence Lipschitz
with constant its operator norm: meanings within `ε` of each other produce forms within
`‖production‖ * ε` of each other. This is the quantitative form of the papers' form–meaning
isomorphy claims ([chuang-bell-tseng-baayen-2026], [lu-chuang-baayen-2026]).

## References

* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal realizations
  in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [Y. Lu, Y.-Y. Chuang and R. H. Baayen, *The realization of tones in spontaneous spoken
  Taiwan Mandarin* (2026)][lu-chuang-baayen-2026]
-/

namespace Processing.Lexical.Discriminative.LinearDiscriminativeLexicon

variable {F M : Type*} [NormedAddCommGroup F] [NormedAddCommGroup M] [NormedSpace ℝ F]
  [NormedSpace ℝ M] [FiniteDimensional ℝ M] (D : LinearDiscriminativeLexicon ℝ F M)

/-- The production map is Lipschitz with constant its operator norm. -/
theorem lipschitzWith_production :
    LipschitzWith ‖D.production.toContinuousLinearMap‖₊ D.production :=
  D.production.toContinuousLinearMap.lipschitz

/-- Meanings within `ε` of each other produce forms within `‖production‖ * ε`. -/
theorem norm_production_sub_le {e₁ e₂ : M} {ε : ℝ} (h : ‖e₁ - e₂‖ ≤ ε) :
    ‖D.production e₁ - D.production e₂‖ ≤ ‖D.production.toContinuousLinearMap‖ * ε := by
  rw [← dist_eq_norm] at h ⊢
  exact (D.lipschitzWith_production.dist_le_mul e₁ e₂).trans
    (mul_le_mul_of_nonneg_left h (norm_nonneg _))

end Processing.Lexical.Discriminative.LinearDiscriminativeLexicon
