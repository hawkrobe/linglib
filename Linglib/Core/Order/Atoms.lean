/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Atoms

/-!
# Atoms and simple orders

Two rungs of `Mathlib.Order.Atoms`. An element of an order with a bottom is bottom or an atom
exactly when it lies below or is disjoint from every element
(`eq_bot_or_isAtom_iff_forall_le_or_disjoint`), the `PartialOrder` form of the atom half of
mathlib's `IsAtom.not_le_iff_disjoint`; on sets this says that a set is a subsingleton exactly
when it is contained in or disjoint from every set
(`Set.subsingleton_iff_forall_subset_or_disjoint`). In a simple order the only strict pair is
`⊥ < ⊤`: mathlib proves each half (`IsSimpleOrder.eq_bot_of_lt`, `IsSimpleOrder.eq_top_of_lt`)
and the special case `Bool.lt_iff`, and the characterization holds for every simple order, so a
two-element scale inherits it from its `IsSimpleOrder` instance. `[UPSTREAM]`

## Main results

* `IsAtom.le_or_disjoint`, `eq_bot_or_isAtom_iff_forall_le_or_disjoint`: an atom is below or
  disjoint from every element, and only bottom and the atoms are.
* `Set.subsingleton_iff_forall_subset_or_disjoint`: a set is a subsingleton iff it is contained
  in or disjoint from every set.
* `IsSimpleOrder.lt_iff_eq_bot_and_eq_top`: `a < b` exactly when `a = ⊥` and `b = ⊤`.
-/

@[expose] public section

section OrderBot

variable {α : Type*} [PartialOrder α] [OrderBot α] {a b : α}

/-- An atom lies below or is disjoint from every element. -/
theorem IsAtom.le_or_disjoint (ha : IsAtom a) (b : α) : a ≤ b ∨ Disjoint a b :=
  or_iff_not_imp_left.2 fun hab _ hxa hxb ↦
    ((ha.le_iff.1 hxa).resolve_right fun h ↦ hab (h ▸ hxb)).le

/-- Bottom and the atoms are exactly the elements below or disjoint from every element. -/
theorem eq_bot_or_isAtom_iff_forall_le_or_disjoint :
    a = ⊥ ∨ IsAtom a ↔ ∀ b, a ≤ b ∨ Disjoint a b := by
  refine ⟨?_, fun h ↦ or_iff_not_imp_left.2 fun hne ↦ ⟨hne, fun b hb ↦ ?_⟩⟩
  · rintro (rfl | ha) b
    exacts [.inl bot_le, ha.le_or_disjoint b]
  · exact (h b).elim (fun hab ↦ absurd hab hb.not_ge) (·.eq_bot_of_ge hb.le)

end OrderBot

/-- A set is a subsingleton iff it is contained in or disjoint from every set. -/
theorem Set.subsingleton_iff_forall_subset_or_disjoint {α : Type*} {s : Set α} :
    s.Subsingleton ↔ ∀ t, s ⊆ t ∨ Disjoint s t := by
  rw [Set.subsingleton_iff_eq_empty_or_singleton, ← Set.isAtom_iff, ← Set.bot_eq_empty]
  exact eq_bot_or_isAtom_iff_forall_le_or_disjoint

namespace IsSimpleOrder

variable {α : Type*} [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] {a b : α}

theorem lt_iff_eq_bot_and_eq_top : a < b ↔ a = ⊥ ∧ b = ⊤ :=
  ⟨fun h ↦ ⟨eq_bot_of_lt h, eq_top_of_lt h⟩, fun ⟨ha, hb⟩ ↦ ha ▸ hb ▸ bot_lt_top⟩

end IsSimpleOrder
