module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Compare

/-!
# Composition of comparisons

This file defines the composition of two comparison results. In a linear order the comparison of
`a` with `c` is constrained by the comparisons of `a` with `b` and of `b` with `c`: two `lt`
compose to `lt`, `eq` is an identity, and `lt` followed by `gt` leaves the result open.
`Ordering.comp o₁ o₂` is the set of results compatible with `o₁` followed by `o₂`, and
`compare_mem_comp` shows that the actual comparison lies in it. It is the point case of the
composition of Allen's interval relations in `Core/Order/AllenRelation.lean`.

## Main declarations

* `Ordering.comp`: the composition table on `Ordering`.
* `Ordering.compare_mem_comp`: `compare a c` lies in `(compare a b).comp (compare b c)`.
-/

@[expose] public section

namespace Ordering

/-- The results of comparing `a` with `c` compatible with `a` comparing to `b` as `o₁` and `b`
to `c` as `o₂`, in a linear order. -/
def comp : Ordering → Ordering → Finset Ordering
  | lt, lt => {lt}
  | lt, eq => {lt}
  | lt, gt => ⊤
  | eq, o => {o}
  | gt, lt => ⊤
  | gt, eq => {gt}
  | gt, gt => {gt}

@[simp] theorem eq_comp (o : Ordering) : eq.comp o = {o} := rfl

@[simp] theorem comp_eq (o : Ordering) : o.comp eq = {o} := by cases o <;> rfl

/-- Reversing both comparisons reverses the composition. -/
theorem image_swap_comp (o₁ o₂ : Ordering) : (o₁.comp o₂).image swap = o₂.swap.comp o₁.swap := by
  revert o₁ o₂; decide

theorem compare_mem_comp {α : Type*} [LinearOrder α] (a b c : α) :
    compare a c ∈ (compare a b).comp (compare b c) := by
  rcases h₁ : compare a b with _ | _ | _ <;> rcases h₂ : compare b c with _ | _ | _ <;>
    simp only [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt] at h₁ h₂ <;>
    simp [comp, compare_lt_iff_lt, compare_gt_iff_gt, h₁, h₂] <;>
    first
      | exact h₁.trans h₂ | exact h₂.trans h₁ | exact h₁.trans_eq h₂ | exact h₁.trans_lt h₂
      | exact h₂.symm.trans_lt h₁

end Ordering
