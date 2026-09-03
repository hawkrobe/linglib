import Mathlib.LinearAlgebra.AffineSpace.Centroid

/-!
# Centroids under affine and linear maps

`[UPSTREAM]` Affine maps commute with the centroids of nonempty finite families of points, the
centroid case of `Finset.map_affineCombination`; so do linear maps, a module being an affine space
over itself; and in a module the centroid is the average of the points.
-/

open Affine

namespace Finset

variable {k V P V₂ P₂ ι : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]
  [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (s : Finset ι)

/-- Affine maps commute with centroids, if the number of points, converted to `k`, is not zero. -/
theorem map_centroid_of_cast_card_ne_zero (p : ι → P) (f : P →ᵃ[k] P₂) (h : (#s : k) ≠ 0) :
    f (s.centroid k p) = s.centroid k (f ∘ p) := by
  rw [centroid_def, centroid_def,
    s.map_affineCombination p _ (s.sum_centroidWeights_eq_one_of_cast_card_ne_zero h)]

/-- In the characteristic zero case, affine maps commute with centroids of nonempty sets. -/
theorem map_centroid_of_nonempty [CharZero k] (p : ι → P) (f : P →ᵃ[k] P₂) (h : s.Nonempty) :
    f (s.centroid k p) = s.centroid k (f ∘ p) :=
  s.map_centroid_of_cast_card_ne_zero p f (Nat.cast_ne_zero.2 (card_pos.2 h).ne')

/-- The centroid of points of a module is their average, if the number of points, converted to
`k`, is not zero. -/
theorem centroid_eq_smul_sum (p : ι → V) (h : (#s : k) ≠ 0) :
    s.centroid k p = (#s : k)⁻¹ • ∑ i ∈ s, p i := by
  rw [centroid_def, s.affineCombination_eq_linear_combination p _
    (s.sum_centroidWeights_eq_one_of_cast_card_ne_zero h), smul_sum]
  simp only [centroidWeights_apply]

end Finset

/-- In the characteristic zero case, linear maps commute with centroids of nonempty sets. -/
theorem LinearMap.map_centroid {k V V₂ ι : Type*} [DivisionRing k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddCommGroup V₂] [Module k V₂] (f : V →ₗ[k] V₂) {s : Finset ι} (h : s.Nonempty)
    (p : ι → V) : f (s.centroid k p) = s.centroid k (f ∘ p) :=
  s.map_centroid_of_nonempty p f.toAffineMap h
