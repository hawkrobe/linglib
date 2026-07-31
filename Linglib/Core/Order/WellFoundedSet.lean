/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.WellFoundedSet

/-!
# Higman's lemma for words

Over a finite alphabet the sublist order on `List α` is a well-quasi-order, specialising
mathlib's `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` to equality.
-/

namespace List

/-- **Higman's lemma** for words [higman-1952]: over a finite alphabet the sublist order is a
well-quasi-order, so every infinite sequence of words has an earlier term embedding in a later
one. -/
theorem wellQuasiOrdered_sublist {α : Type*} [Finite α] :
    WellQuasiOrdered (fun l₁ l₂ : List α => l₁ <+ l₂) := fun f => by
  obtain ⟨m, n, hmn, h⟩ := Set.PartiallyWellOrderedOn.exists_lt
    (Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ (Eq : α → α → Prop)
      Set.finite_univ.partiallyWellOrderedOn) (f := f) fun _ _ _ => Set.mem_univ _
  exact ⟨m, n, hmn, by simpa [sublistForall₂_iff, forall₂_eq_eq_eq] using h⟩

end List
