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
* `IsLowerSet.subset_iff_card_le` — lower finsets of a linear order are nested by size, so they
  form a chain (the `LinearOrder` instance on the subtype).
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

variable {t : Finset α}

/-- Lower finsets of a linear order are nested. [UPSTREAM] -/
theorem IsLowerSet.subset_or_subset (hs : IsLowerSet (↑s : Set α))
    (ht : IsLowerSet (↑t : Set α)) : s ⊆ t ∨ t ⊆ s := by
  simpa using hs.total ht

/-- Among lower finsets of a linear order, inclusion is comparison of sizes. [UPSTREAM] -/
theorem IsLowerSet.subset_iff_card_le (hs : IsLowerSet (↑s : Set α))
    (ht : IsLowerSet (↑t : Set α)) : s ⊆ t ↔ s.card ≤ t.card :=
  ⟨card_le_card, fun h ↦ (hs.subset_or_subset ht).elim id fun hts ↦ by
    rw [eq_of_subset_of_card_le hts h]⟩

/-- Lower finsets of a linear order are determined by their sizes. [UPSTREAM] -/
theorem IsLowerSet.eq_iff_card_eq (hs : IsLowerSet (↑s : Set α))
    (ht : IsLowerSet (↑t : Set α)) : s = t ↔ s.card = t.card :=
  ⟨congrArg _, fun h ↦ Subset.antisymm ((hs.subset_iff_card_le ht).2 h.le)
    ((ht.subset_iff_card_le hs).2 h.ge)⟩

/-- The lower finsets of a linear order form a chain under inclusion, the order of their
sizes: the rungs of an implicational hierarchy. [UPSTREAM] -/
instance : LinearOrder {s : Finset α // IsLowerSet (↑s : Set α)} where
  __ := (inferInstance : PartialOrder {s : Finset α // IsLowerSet (↑s : Set α)})
  le_total s t := s.2.subset_or_subset t.2
  toDecidableLE s t := inferInstanceAs (Decidable (s.1 ⊆ t.1))
  toDecidableEq := inferInstance
  toDecidableLT s t := inferInstanceAs (Decidable (s.1 ⊂ t.1))

theorem IsLowerSet.subtype_le_iff_card_le {s t : {s : Finset α // IsLowerSet (↑s : Set α)}} :
    s ≤ t ↔ s.1.card ≤ t.1.card :=
  s.2.subset_iff_card_le t.2

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
