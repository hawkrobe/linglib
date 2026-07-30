/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.FreeMonoid.FreeSemigroup`, next to
`FreeMonoid.equivWithOneFreeSemigroup`.
-/
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Algebra.FreeMonoid.FreeSemigroup

/-!
# The free monoid as the unitization of the free semigroup

`FreeMonoid.equivWithOneFreeSemigroup` sends the image of `FreeSemigroup.toFreeMonoid` to the
`WithOne` coercion, and a homomorphism out of the free semigroup extends along it to the free
monoid (`FreeMonoid.mapWithOne`), with the empty word sent to `1`.
-/

variable {α : Type*} (u : FreeSemigroup α)

theorem FreeMonoid.equivWithOneFreeSemigroup_toFreeMonoid :
    equivWithOneFreeSemigroup u.toFreeMonoid = ↑u := by
  rw [show (u.toFreeMonoid : FreeMonoid α) =
    equivWithOneFreeSemigroup.symm ↑u from rfl, MulEquiv.apply_symm_apply]

@[simp] theorem FreeSemigroup.toList_toFreeMonoid_ne_nil :
    u.toFreeMonoid.toList ≠ [] := fun h =>
  toFreeMonoid_ne_one u (FreeMonoid.toList.injective h)

variable {T : Type*} [Mul T] (η : FreeSemigroup α →ₙ* T)

/-- The extension of a homomorphism out of the free semigroup to the free monoid, with the
empty word sent to `1`. -/
def FreeMonoid.mapWithOne : FreeMonoid α →* WithOne T :=
  (WithOne.mapMulHom η).comp equivWithOneFreeSemigroup.toMonoidHom

@[simp] theorem FreeMonoid.mapWithOne_toFreeMonoid :
    mapWithOne η u.toFreeMonoid = ↑(η u) := by
  rw [mapWithOne, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    equivWithOneFreeSemigroup_toFreeMonoid, WithOne.mapMulHom_coe]

@[simp] theorem FreeMonoid.mapWithOne_ofList_cons (c : α) (l : List α) :
    mapWithOne η (.ofList (c :: l)) = ↑(η ⟨c, l⟩) := by
  rw [← FreeSemigroup.toFreeMonoid_mk_eq_cons, mapWithOne_toFreeMonoid]
