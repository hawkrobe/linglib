/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer

/-!
# Homogeneous components of the Connes–Kreimer algebra

As an algebra, `ConnesKreimer R T` is the polynomial algebra in the trees, graded by the number
of trees in a forest. `homogeneousComponent k` projects onto the span of the forests with `k`
trees, as `MvPolynomial.homogeneousComponent` does for total degree.

## Main declarations

* `ConnesKreimer.homogeneousComponent k`: the projection onto the forests with `k` trees.
* `ConnesKreimer.homogeneousComponent_comp_homogeneousComponent`: the projections are orthogonal
  idempotents.

## Implementation notes

The grading is by number of trees, not by number of vertices. A grading by vertices would be a
weighted version (`MvPolynomial.weightedHomogeneousComponent`), with each tree weighted by its
size.

## References

* [connes-kreimer-1998]
-/

@[expose] public section

namespace ConnesKreimer

open UnorderedTree

variable {R : Type*} [CommSemiring R] {T : Type*}

/-- The degree-`k` homogeneous component is the projection onto the span of the forests with
exactly `k` trees. -/
noncomputable def homogeneousComponent (k : ℕ) : ConnesKreimer R T →ₗ[R] ConnesKreimer R T :=
  linearLift fun F ↦ if F.card = k then of' F else 0

@[simp] theorem homogeneousComponent_of' (k : ℕ) (F : Forest T) :
    homogeneousComponent k (of' (R := R) F) = if F.card = k then of' F else 0 :=
  linearLift_of' _ F

@[simp] theorem homogeneousComponent_ofTree (k : ℕ) (t : T) :
    homogeneousComponent k (ofTree (R := R) t) = if 1 = k then ofTree t else 0 := by
  rw [← of'_singleton, homogeneousComponent_of', Multiset.card_singleton]

@[simp] theorem homogeneousComponent_one (k : ℕ) :
    homogeneousComponent k (1 : ConnesKreimer R T) = if 0 = k then 1 else 0 := by
  rw [← of'_zero, homogeneousComponent_of', Multiset.card_zero]

theorem homogeneousComponent_comp_homogeneousComponent (j k : ℕ) :
    (homogeneousComponent j).comp (homogeneousComponent (R := R) (T := T) k) =
      if j = k then homogeneousComponent k else 0 := by
  refine lhom_ext' fun F ↦ ?_
  simp only [LinearMap.comp_apply, homogeneousComponent_of']
  split_ifs <;> simp_all [eq_comm]

end ConnesKreimer
