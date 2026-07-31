/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.WellFoundedSet

/-!
# Higman's lemma for sublists

For a finite type `α` the sublist order on `List α` is a well-quasi-order, specialising
mathlib's `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` to equality.
-/

namespace List

/-- **Higman's lemma** [higman-1952]: for a finite type `α` the sublist order on `List α` is a
well-quasi-order — every infinite sequence of lists has an earlier term that is a sublist of a
later one. -/
theorem wellQuasiOrdered_sublist {α : Type*} [Finite α] :
    WellQuasiOrdered (fun l₁ l₂ : List α => l₁ <+ l₂) := fun f => by
  obtain ⟨m, n, hmn, h⟩ := Set.PartiallyWellOrderedOn.exists_lt
    (Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ (Eq : α → α → Prop)
      Set.finite_univ.partiallyWellOrderedOn) (f := f) fun _ _ _ => Set.mem_univ _
  exact ⟨m, n, hmn, by simpa [sublistForall₂_iff, forall₂_eq_eq_eq] using h⟩

end List
