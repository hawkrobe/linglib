import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

/-!
# Lower sets carried by finsets

The lower-set predicate on the coercion of a finset, `IsLowerSet (↑s : Set α)`,
is decidable over a finite type with decidable order — the `[UPSTREAM]`
candidate here — and the lower sets contained in a finset form a finset, closed
under removing an element together with everything above it. In a linear order a
lower finset is the initial segment up to its maximum, which is how an
implicational hierarchy places a language on a rung.

## Main declarations

* `IsLowerSet.mem_iff_le_max` — a lower finset of a linear order is `Iic` of its max.
* `Finset.lowerSubsets` — the lower sets contained in a finset.
* `Finset.filter_not_le_mem_lowerSubsets` — removing an upper cone stays inside.
-/

open Finset

section LinearOrder

variable {α : Type*} [LinearOrder α] {s : Finset α} {a : α}

/-- A lower finset of a linear order is the initial segment up to its maximum. [UPSTREAM] -/
theorem IsLowerSet.mem_iff_le_max (h : IsLowerSet (↑s : Set α)) : a ∈ s ↔ ↑a ≤ s.max := by
  refine ⟨le_max, fun ha ↦ ?_⟩
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 (ne_bot_of_le_ne_bot WithBot.coe_ne_bot ha)
  exact h (WithBot.coe_le_coe.1 (hm ▸ ha)) (mem_of_max hm.symm)

/-- An upper finset of a linear order is the final segment from its minimum. [UPSTREAM] -/
theorem IsUpperSet.mem_iff_min_le (h : IsUpperSet (↑s : Set α)) : a ∈ s ↔ s.min ≤ ↑a := by
  refine ⟨min_le, fun ha ↦ ?_⟩
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top ha)
  exact h (WithTop.coe_le_coe.1 (hm ▸ ha)) (mem_of_min hm.symm)

end LinearOrder

variable {α : Type*} [Preorder α] [Fintype α] [DecidableEq α] [DecidableLE α] {s t : Finset α}

instance (s : Finset α) : Decidable (IsLowerSet (↑s : Set α)) :=
  decidable_of_iff (∀ a ∈ s, ∀ b, b ≤ a → b ∈ s) <| by
    simp only [IsLowerSet, mem_coe]
    exact ⟨fun h _ _ hb ha => h _ ha _ hb, fun h a ha b hb => h hb ha⟩

/-- The lower sets contained in `t`. -/
def Finset.lowerSubsets (t : Finset α) : Finset (Finset α) :=
  t.powerset.filter fun s => IsLowerSet (↑s : Set α)

@[simp] theorem Finset.mem_lowerSubsets :
    s ∈ t.lowerSubsets ↔ s ⊆ t ∧ IsLowerSet (↑s : Set α) := by
  simp [lowerSubsets]

theorem Finset.filter_not_le_mem_lowerSubsets (h : s ∈ t.lowerSubsets) (a : α) :
    (s.filter fun b => ¬ a ≤ b) ∈ t.lowerSubsets := by
  rw [mem_lowerSubsets] at h ⊢
  refine ⟨(filter_subset _ _).trans h.1, ?_⟩
  convert h.2.sdiff_of_isUpperSet (isUpperSet_Ici a) using 1
  ext; simp
