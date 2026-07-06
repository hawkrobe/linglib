import Linglib.Processing.Lexical.Discriminative.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# DLM in normed carriers
[baayen-2019] [chuang-bell-tseng-baayen-2026] [lu-chuang-baayen-2026]
[heitmeier-chuang-baayen-2026]

Over finite-dimensional real normed carriers the DLM's maps are automatically
continuous, so the papers' quantitative form-meaning isomorphism claims can be
stated via operator norms.

## Main declarations

- `dlm_lipschitz_production` / `dlm_lipschitz_comprehension`: each map is
  Lipschitz with constant its operator norm.
- `dlm_neighbor_centroids_imply_neighbor_contours`: meanings within `ε`
  produce forms within `‖production‖ * ε`.
- `LinearDiscriminativeLexicon.IsMeaningApproxIso` / `IsFormApproxIso`:
  approximate-inverse round-trip properties.

## Implementation notes

Lipschitz theorems require `[FiniteDimensional ℝ ·]` on the relevant map's
source so `LinearMap.toContinuousLinearMap` applies. The carrier fixes the
norm in the bound: `Fin n → ℝ` carries the sup norm, which suffices for
direction-of-effect arguments; studies needing the Euclidean norm (e.g. for
cosine-similarity statements) should use `EuclideanSpace ℝ (Fin n)`.
-/

namespace Processing.Lexical.Discriminative

/-! ### Lipschitz continuity of the production map -/

section Lipschitz

variable {F M : Type*}
  [NormedAddCommGroup F] [NormedAddCommGroup M]
  [NormedSpace ℝ F] [NormedSpace ℝ M]

/-- The production map is Lipschitz with constant its operator norm. -/
theorem dlm_lipschitz_production
    [FiniteDimensional ℝ M]
    (D : LinearDiscriminativeLexicon ℝ F M) (e₁ e₂ : M) :
    ‖D.production e₁ - D.production e₂‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ‖e₁ - e₂‖ := by
  rw [← map_sub]
  exact D.production.toContinuousLinearMap.le_opNorm _

/-- Dual of `dlm_lipschitz_production` for the form → meaning direction. -/
theorem dlm_lipschitz_comprehension
    [FiniteDimensional ℝ F]
    (D : LinearDiscriminativeLexicon ℝ F M) (f₁ f₂ : F) :
    ‖D.comprehension f₁ - D.comprehension f₂‖ ≤
      ‖D.comprehension.toContinuousLinearMap‖ * ‖f₁ - f₂‖ := by
  rw [← map_sub]
  exact D.comprehension.toContinuousLinearMap.le_opNorm _

end Lipschitz

/-! ### Neighbor preservation -/

section NeighborPreservation

variable {F M : Type*}
  [NormedAddCommGroup F] [NormedAddCommGroup M]
  [NormedSpace ℝ F] [NormedSpace ℝ M]

/-- **Neighbor centroids → neighbor contours**: meanings within `ε` of each
    other produce forms within `‖production‖ * ε` of each other. -/
theorem dlm_neighbor_centroids_imply_neighbor_contours
    [FiniteDimensional ℝ M]
    (D : LinearDiscriminativeLexicon ℝ F M) {e₁ e₂ : M} {ε : ℝ}
    (h : ‖e₁ - e₂‖ ≤ ε) :
    ‖D.production e₁ - D.production e₂‖ ≤
      ‖D.production.toContinuousLinearMap‖ * ε :=
  (dlm_lipschitz_production D e₁ e₂).trans <|
    mul_le_mul_of_nonneg_left h (ContinuousLinearMap.opNorm_nonneg _)

end NeighborPreservation

/-! ### Approximate-inverse / form-meaning ε-isomorphism -/

section ApproximateInverse

variable {F M : Type*}
  [NormedAddCommGroup F] [NormedAddCommGroup M]
  [NormedSpace ℝ F] [NormedSpace ℝ M]

/-- `D` is an `ε`-approximate isomorphism on the meaning side: every
    round-trip `comprehension (production e)` returns within `ε` of `e`. -/
def LinearDiscriminativeLexicon.IsMeaningApproxIso
    (D : LinearDiscriminativeLexicon ℝ F M) (ε : ℝ) : Prop :=
  ∀ e : M, ‖D.comprehension (D.production e) - e‖ ≤ ε

/-- Dual of `IsMeaningApproxIso`: every round-trip
    `production (comprehension f)` returns within `ε` of `f`. -/
def LinearDiscriminativeLexicon.IsFormApproxIso
    (D : LinearDiscriminativeLexicon ℝ F M) (ε : ℝ) : Prop :=
  ∀ f : F, ‖D.production (D.comprehension f) - f‖ ≤ ε

/-- The `ε = 0` case of `IsMeaningApproxIso`: comprehension is a left
    inverse of production. -/
theorem LinearDiscriminativeLexicon.isMeaningApproxIso_zero_iff
    (D : LinearDiscriminativeLexicon ℝ F M) :
    D.IsMeaningApproxIso 0 ↔ ∀ e : M, D.comprehension (D.production e) = e := by
  unfold LinearDiscriminativeLexicon.IsMeaningApproxIso
  refine ⟨fun h e => ?_, fun h e => ?_⟩
  · have hn : ‖D.comprehension (D.production e) - e‖ = 0 :=
      le_antisymm (h e) (norm_nonneg _)
    rwa [norm_eq_zero, sub_eq_zero] at hn
  · rw [h e, sub_self, norm_zero]

end ApproximateInverse

end Processing.Lexical.Discriminative
