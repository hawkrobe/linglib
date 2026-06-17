import Mathlib.Order.Compare
import Mathlib.Data.Finset.Basic

/-!
# Comparison categories

A **comparison category** is a `Finset Ordering` — which of `lt`/`eq`/`gt` a pair of elements of a
linear order may stand in. The atomic categories are the singletons (mathlib `Ordering` itself);
unions like `≤`/`≥` are larger sets. `holds s a b` says the comparison of `a` and `b` falls in `s`.

This is framework-agnostic order theory (the point analogue of `AllenRelation` for intervals): it is
generic over any `[LinearOrder α]` and bakes in **no** notion of time. Tense, evidential, and
modal-base-time semantics each supply the order (`Time`) and name the categories they use
(`Tense.past = before`, etc.).
-/

namespace Core.Order

variable {α : Type*} [LinearOrder α]

/-- A pair `a, b` stands in comparison category `s` iff `compare a b` is one of `s`'s orderings. -/
def holds (s : Finset Ordering) (a b : α) : Prop := compare a b ∈ s

instance (s : Finset Ordering) (a b : α) : Decidable (holds s a b) :=
  inferInstanceAs (Decidable (_ ∈ s))

/-! ### Named comparison categories -/

/-- `a < b`. -/
def before : Finset Ordering := {.lt}
/-- `a > b`. -/
def after : Finset Ordering := {.gt}
/-- `a = b` (points overlap). -/
def overlapping : Finset Ordering := {.eq}
/-- `a ≤ b`. -/
def notAfter : Finset Ordering := {.lt, .eq}
/-- `a ≥ b`. -/
def notBefore : Finset Ordering := {.gt, .eq}
/-- no constraint. -/
def unrestricted : Finset Ordering := {.lt, .eq, .gt}

/-! ### Reductions to the underlying order (so consumers' `<`-shaped proofs go through) -/

@[simp] theorem holds_before (a b : α) : holds before a b ↔ a < b := by
  simp [holds, before, compare_lt_iff_lt]
@[simp] theorem holds_after (a b : α) : holds after a b ↔ b < a := by
  simp [holds, after, compare_gt_iff_gt]
@[simp] theorem holds_overlapping (a b : α) : holds overlapping a b ↔ a = b := by
  simp [holds, overlapping]
@[simp] theorem holds_notAfter (a b : α) : holds notAfter a b ↔ a ≤ b := by
  simp [holds, notAfter, compare_lt_iff_lt, le_iff_lt_or_eq]
@[simp] theorem holds_notBefore (a b : α) : holds notBefore a b ↔ b ≤ a := by
  rw [← not_lt, ← compare_lt_iff_lt]
  simp only [holds, notBefore, Finset.mem_insert, Finset.mem_singleton]
  cases compare a b <;> simp
@[simp] theorem holds_unrestricted (a b : α) : holds unrestricted a b ↔ True := by
  simp only [holds, unrestricted, iff_true]
  rcases lt_trichotomy a b with h | h | h
  · simp [compare_lt_iff_lt.mpr h]
  · simp [compare_eq_iff_eq.mpr h]
  · simp [compare_gt_iff_gt.mpr h]

end Core.Order
