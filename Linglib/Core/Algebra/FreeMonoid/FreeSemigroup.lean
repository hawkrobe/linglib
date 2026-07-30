/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.FreeMonoid.FreeSemigroup`, next to
`FreeMonoid.equivWithOneFreeSemigroup`.
-/
import Mathlib.Algebra.FreeMonoid.FreeSemigroup

/-!
# The free monoid-with-one equivalence on `toFreeMonoid`

`FreeMonoid.equivWithOneFreeSemigroup` sends the image of `FreeSemigroup.toFreeMonoid` to the
`WithOne` coercion.
-/

variable {α : Type*} (u : FreeSemigroup α)

theorem FreeMonoid.equivWithOneFreeSemigroup_toFreeMonoid :
    equivWithOneFreeSemigroup (FreeSemigroup.toFreeMonoid u) = ↑u := by
  rw [show (FreeSemigroup.toFreeMonoid u : FreeMonoid α) =
    equivWithOneFreeSemigroup.symm ↑u from rfl, MulEquiv.apply_symm_apply]

@[simp] theorem FreeSemigroup.toList_toFreeMonoid_ne_nil :
    FreeMonoid.toList (toFreeMonoid u) ≠ [] := fun h =>
  toFreeMonoid_ne_one u (FreeMonoid.toList.injective h)
