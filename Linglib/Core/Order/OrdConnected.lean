import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Order-connected finite sets are closed intervals

`[UPSTREAM]` candidate for `Mathlib/Order/Interval/Finset/Basic.lean`: a nonempty finset in a
locally finite linear order is order-connected iff it is the closed interval between its least
and greatest elements. This is the shape of a "contiguous segment of a hierarchy" wherever a
linguistic scale is linearly ordered and a strategy covers a run of it.

## Main statements

* `Finset.ordConnected_coe_iff_eq_Icc`
* `Finset.eq_Icc_top_of_ordConnected`: with a top element in the set, the interval reaches it.
* `Finset.isUpperSet_coe_of_ordConnected`: such a set is an upper set.
-/

namespace Finset

variable {α : Type*}

section Preorder

variable [Preorder α] {s : Finset α}

/-- Order-connectedness of a finset is decided on its closed intervals. -/
instance [DecidableEq α] [LocallyFiniteOrder α] (s : Finset α) :
    Decidable (s : Set α).OrdConnected :=
  decidable_of_iff (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ Icc x y, z ∈ s) <| by
    simp only [Set.ordConnected_iff, Set.subset_def, Set.mem_Icc, mem_coe, mem_Icc, and_imp]
    exact ⟨fun h x hx y hy _ z hxz hzy ↦ h x hx y hy z hxz hzy,
      fun h x hx y hy z hxz hzy ↦ h x hx y hy (hxz.trans hzy) z hxz hzy⟩

/-- An order-connected finset containing the top element is an upper set. -/
theorem isUpperSet_coe_of_ordConnected [OrderTop α] (hc : (s : Set α).OrdConnected)
    (ht : ⊤ ∈ s) : IsUpperSet (s : Set α) :=
  fun _ _ hab ha ↦ hc.out ha ht ⟨hab, le_top⟩

end Preorder

variable [LinearOrder α] [LocallyFiniteOrder α] {s : Finset α}

/-- A nonempty finset is order-connected iff it is the closed interval from its least to its
greatest element. -/
theorem ordConnected_coe_iff_eq_Icc (hs : s.Nonempty) :
    (s : Set α).OrdConnected ↔ s = Icc (s.min' hs) (s.max' hs) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext x
    simp only [mem_Icc]
    exact ⟨fun hx ↦ ⟨min'_le _ _ hx, le_max' _ _ hx⟩,
      fun hx ↦ h.out (min'_mem _ _) (max'_mem _ _) hx⟩
  · have : (s : Set α) = Set.Icc (s.min' hs) (s.max' hs) := by
      rw [← coe_Icc]; exact congrArg _ h
    rw [this]; exact Set.ordConnected_Icc

/-- An order-connected finset containing the top element is the closed interval from its least
element up to the top. -/
theorem eq_Icc_top_of_ordConnected [OrderTop α] (hc : (s : Set α).OrdConnected) (ht : ⊤ ∈ s) :
    s = Icc (s.min' ⟨⊤, ht⟩) ⊤ := by
  ext p
  simp only [mem_Icc, le_top, and_true]
  exact ⟨min'_le _ _, fun h ↦ hc.out (min'_mem _ _) ht ⟨h, le_top⟩⟩

end Finset
