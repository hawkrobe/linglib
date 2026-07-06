import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Least-squares solutions

`IsLeastSquares A b x` says `x` minimises `‖A y − b‖` over the domain of a
linear map `A` into a real inner product space. Mathlib provides the
subspace side (`Submodule.starProjection` and its minimality); this file
packages the pulled-back problem: the first-order characterisation,
existence, uniqueness of fitted values, and the solution coset.

`[UPSTREAM]` candidate — mathlib has the ingredients but not the packaging;
generalises from `ℝ` to `RCLike 𝕜`.

## Main declarations

* `IsLeastSquares A b x`: `x` minimises `‖A y − b‖`.
* `isLeastSquares_iff_inner_eq_zero`: the first-order characterisation —
  the residual is orthogonal to the range of `A` (the *normal equations*).
* `exists_isLeastSquares`: solutions exist whenever the range of `A` admits
  an orthogonal projection (in particular in finite dimension).
* `IsLeastSquares.map_eq`: fitted values are unique.
* `IsLeastSquares.iff_map_eq`: the solutions are exactly the preimages of
  the fitted value.
-/

namespace Core

open RealInnerProductSpace

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (A : E →ₗ[ℝ] F) (b : F)

/-- `x` is a **least-squares solution** of `A y ≈ b` if it minimises the
    residual norm `‖A y − b‖`. -/
def IsLeastSquares (x : E) : Prop := ∀ y, ‖A x - b‖ ≤ ‖A y - b‖

variable {A b}

/-- The first-order characterisation of least squares: `x` is a solution iff
    the residual `b − A x` is orthogonal to everything `A` can produce —
    the **normal equations**, with no rank hypothesis. -/
theorem isLeastSquares_iff_inner_eq_zero {x : E} :
    IsLeastSquares A b x ↔ ∀ y, ⟪b - A x, A y⟫ = 0 := by
  constructor
  · intro hx
    have heq : ‖b - A x‖ = ⨅ w : LinearMap.range A, ‖b - ↑w‖ := by
      refine le_antisymm (le_ciInf fun w => ?_) ?_
      · obtain ⟨y, hy⟩ := w.2
        rw [← hy]
        simpa [norm_sub_rev] using hx y
      · have hbdd : BddBelow (Set.range fun w : LinearMap.range A => ‖b - ↑w‖) :=
          ⟨0, by rintro r ⟨w, rfl⟩; exact norm_nonneg _⟩
        exact ciInf_le hbdd ⟨A x, LinearMap.mem_range_self A x⟩
    intro y
    exact ((LinearMap.range A).norm_eq_iInf_iff_real_inner_eq_zero
      (LinearMap.mem_range_self A x)).mp heq (A y) (LinearMap.mem_range_self A y)
  · intro h y
    have hsq : ‖b - A y‖ ^ 2
        = ‖b - A x‖ ^ 2 + ‖A x - A y‖ ^ 2 := by
      have hdecomp : b - A y = (b - A x) + (A x - A y) := by abel
      rw [hdecomp, norm_add_sq_real, ← map_sub, h (x - y), mul_zero, add_zero]
    have hle : ‖b - A x‖ ^ 2 ≤ ‖b - A y‖ ^ 2 := by
      nlinarith [sq_nonneg ‖A x - A y‖]
    have hroot := Real.sqrt_le_sqrt hle
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hroot
    simpa [norm_sub_rev] using hroot

/-- Least-squares solutions exist whenever the range of `A` admits an
    orthogonal projection — in particular whenever it is finite-dimensional. -/
theorem exists_isLeastSquares [(LinearMap.range A).HasOrthogonalProjection] :
    ∃ x, IsLeastSquares A b x := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp
    ((LinearMap.range A).starProjection_apply_mem b)
  exact ⟨x, isLeastSquares_iff_inner_eq_zero.mpr fun y => hx ▸
    Submodule.starProjection_inner_eq_zero b (A y) (LinearMap.mem_range_self A y)⟩

/-- Fitted values are unique: any two least-squares solutions produce the
    same point of the range. -/
theorem IsLeastSquares.map_eq {x x' : E}
    (hx : IsLeastSquares A b x) (hx' : IsLeastSquares A b x') :
    A x = A x' := by
  have h := isLeastSquares_iff_inner_eq_zero.mp hx
  have h' := isLeastSquares_iff_inner_eq_zero.mp hx'
  have key : ∀ y, ⟪A x - A x', A y⟫ = 0 := fun y => by
    have hd : A x - A x' = (b - A x') - (b - A x) := by abel
    rw [hd, inner_sub_left, h y, h' y, sub_zero]
  have h0 := key (x - x')
  rw [map_sub] at h0
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp h0)

/-- The least-squares solutions are exactly the preimages of the fitted
    value: given one solution, another point solves iff it maps to the same
    place. -/
theorem IsLeastSquares.iff_map_eq {x x' : E} (hx : IsLeastSquares A b x) :
    IsLeastSquares A b x' ↔ A x' = A x :=
  ⟨fun hx' => hx'.map_eq hx, fun h y => h ▸ hx y⟩

/-- Under an injective design map the least-squares solution is unique. -/
theorem IsLeastSquares.eq_of_injective (hA : Function.Injective A) {x x' : E}
    (hx : IsLeastSquares A b x) (hx' : IsLeastSquares A b x') : x = x' :=
  hA (hx.map_eq hx')

end Core
