/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.FreeSemigroup

/-!
# The word underlying a free-semigroup element

`FreeSemigroup.toList` presents a free-semigroup element as the nonempty word `head :: tail`.

Mathlib's `FreeSemigroup.toFreeMonoid` is the same map bundled as a `→ₙ*`, but built by the
universal property, so its multiplicativity is the theorem `map_mul` rather than `rfl`. This file
keeps the structural version, whose `rfl` is what quotient constructions over `FreeSemigroup α`
rely on, and relates the two by `FreeSemigroup.toFreeMonoid_eq_ofList` — the single point of
contact, from which the remaining lemmas are derived rather than reproved.
-/

namespace FreeSemigroup

variable {α : Type*} (u v : FreeSemigroup α)

/-- The nonempty word underlying a free-semigroup element. -/
def toList : List α := u.head :: u.tail

/-- Multiplication is concatenation, definitionally — the property that distinguishes this from
mathlib's `FreeSemigroup.toFreeMonoid`. -/
@[simp] theorem toList_mul : (u * v).toList = u.toList ++ v.toList := rfl

theorem toFreeMonoid_eq_ofList : toFreeMonoid u = FreeMonoid.ofList u.toList := by
  cases u; exact toFreeMonoid_mk_eq_cons _ _

/-- The free semigroup is the *nonempty* words. -/
@[simp] theorem toList_ne_nil : u.toList ≠ [] := fun h =>
  toFreeMonoid_ne_one u (by rw [toFreeMonoid_eq_ofList, h]; rfl)

theorem toList_injective : Function.Injective (toList (α := α)) := fun _ _ h =>
  toFreeMonoid_injective (by rw [toFreeMonoid_eq_ofList, toFreeMonoid_eq_ofList, h])

/-- Every word is empty or comes from the free semigroup — the free-level form of
`M_A = S_A ∪ {1}`. -/
theorem eq_nil_or_exists_toList (w : List α) : w = [] ∨ ∃ u : FreeSemigroup α, u.toList = w := by
  rcases eq_one_or_toFreeMonoid (FreeMonoid.ofList w) with h | ⟨u, hu⟩
  · exact Or.inl (FreeMonoid.ofList.injective (h.trans FreeMonoid.ofList_nil.symm))
  · exact Or.inr ⟨u, by simpa [toFreeMonoid_eq_ofList] using hu⟩

end FreeSemigroup
