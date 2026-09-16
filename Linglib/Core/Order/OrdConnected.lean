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
-/

namespace Finset

variable {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] {s : Finset α}

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

end Finset
