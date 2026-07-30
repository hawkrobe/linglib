/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.FreeMonoid.FreeSemigroup`, next to
`FreeSemigroup.toFreeMonoid`.
-/
import Mathlib.Algebra.FreeMonoid.FreeSemigroup

/-!
# The word underlying a free-semigroup element

`FreeSemigroup.toList` presents a free-semigroup element as its nonempty word, by way of
`FreeSemigroup.toFreeMonoid`; every lemma is inherited from the `toFreeMonoid` API.
-/

namespace FreeSemigroup

variable {α : Type*} (u v : FreeSemigroup α)

/-- The nonempty word underlying a free-semigroup element. -/
def toList : List α := (toFreeMonoid u).toList

theorem toFreeMonoid_eq_ofList : toFreeMonoid u = FreeMonoid.ofList u.toList := rfl

@[simp] theorem toList_mk (a : α) (l : List α) : toList ⟨a, l⟩ = a :: l := by
  simp [toList, toFreeMonoid_mk_eq_cons]

@[simp] theorem toList_mul : (u * v).toList = u.toList ++ v.toList := by
  simp [toList, map_mul]

@[simp] theorem toList_ne_nil : u.toList ≠ [] := fun h =>
  toFreeMonoid_ne_one u (FreeMonoid.toList.injective h)

theorem toList_injective : Function.Injective (toList (α := α)) := fun _ _ h =>
  toFreeMonoid_injective (FreeMonoid.toList.injective h)

/-- Every word is empty or comes from the free semigroup. -/
theorem eq_nil_or_exists_toList (w : List α) : w = [] ∨ ∃ u : FreeSemigroup α, u.toList = w := by
  rcases eq_one_or_toFreeMonoid (FreeMonoid.ofList w) with h | ⟨u, hu⟩
  · exact .inl (FreeMonoid.ofList.injective h)
  · exact .inr ⟨u, by simp [toList, hu]⟩

theorem _root_.FreeMonoid.equivWithOneFreeSemigroup_toFreeMonoid (u : FreeSemigroup α) :
    FreeMonoid.equivWithOneFreeSemigroup (toFreeMonoid u) = ↑u := by
  rw [show (toFreeMonoid u : FreeMonoid α) = FreeMonoid.equivWithOneFreeSemigroup.symm ↑u from
    rfl, MulEquiv.apply_symm_apply]

end FreeSemigroup
