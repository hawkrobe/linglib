import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

/-!
# Lower sets carried by finsets

`[UPSTREAM]` candidate for `Mathlib/Order/UpperLower/Finset.lean`: the
lower-set predicate on the coercion of a finset — its first-order
characterization and decidability over a finite type, the lower sets
contained in a finset, and two closure facts: removing an element together
with everything above it preserves lower sets, and an element can be inserted
into a lower set exactly when everything strictly below it is already present.

## Main declarations

* `Finset.isLowerSet_coe_iff` — `IsLowerSet ↑s ↔ ∀ a ∈ s, ∀ b ≤ a, b ∈ s`.
* `Finset.lowerSubsets` — the lower sets contained in a finset.
* `IsLowerSet.filter_not_le` — removing an upper cone preserves lower sets.
* `Finset.isLowerSet_insert_iff` — when insertion preserves lower sets.
-/

open Finset

variable {α : Type*} {s t : Finset α} {a : α}

section Preorder

variable [Preorder α]

theorem Finset.isLowerSet_coe_iff :
    IsLowerSet (↑s : Set α) ↔ ∀ a ∈ s, ∀ b, b ≤ a → b ∈ s := by
  simp only [IsLowerSet, mem_coe]
  exact ⟨fun h a ha b hb => h hb ha, fun h _ _ hb ha => h _ ha _ hb⟩

theorem IsLowerSet.filter_not_le [DecidableLE α] (hs : IsLowerSet (↑s : Set α)) (a : α) :
    IsLowerSet (↑(s.filter fun b => ¬ a ≤ b) : Set α) := by
  convert hs.sdiff_of_isUpperSet (isUpperSet_Ici a) using 1
  ext; simp

end Preorder

theorem Finset.isLowerSet_insert_iff [PartialOrder α] [DecidableEq α]
    (hs : IsLowerSet (↑s : Set α)) :
    IsLowerSet (↑(insert a s) : Set α) ↔ ∀ b, b < a → b ∈ s := by
  refine ⟨fun h b hb => ?_, fun h x y hxy hy => ?_⟩
  · have := h hb.le (mem_insert_self a s)
    rw [mem_coe, mem_insert] at this
    exact this.resolve_left hb.ne
  · rw [mem_coe, mem_insert] at hy ⊢
    rcases hy with rfl | hy
    · exact hxy.lt_or_eq.elim (fun h' => .inr (h _ h')) .inl
    · exact .inr (hs hxy hy)

section Fintype

variable [Preorder α] [Fintype α] [DecidableEq α] [DecidableLE α]

instance (s : Finset α) : Decidable (IsLowerSet (↑s : Set α)) :=
  decidable_of_iff _ isLowerSet_coe_iff.symm

/-- The lower sets contained in `t`. -/
def Finset.lowerSubsets (t : Finset α) : Finset (Finset α) :=
  t.powerset.filter fun s => IsLowerSet (↑s : Set α)

@[simp] theorem Finset.mem_lowerSubsets :
    s ∈ t.lowerSubsets ↔ s ⊆ t ∧ IsLowerSet (↑s : Set α) := by
  simp [lowerSubsets]

theorem Finset.filter_not_le_mem_lowerSubsets (h : s ∈ t.lowerSubsets) (a : α) :
    (s.filter fun b => ¬ a ≤ b) ∈ t.lowerSubsets :=
  mem_lowerSubsets.2 ⟨(filter_subset _ _).trans (mem_lowerSubsets.1 h).1,
    (mem_lowerSubsets.1 h).2.filter_not_le a⟩

end Fintype
