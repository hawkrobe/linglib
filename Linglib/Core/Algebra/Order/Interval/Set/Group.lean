module

public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Projection onto a ray in an ordered group

This file shows that in a linearly ordered additive group the distance of `Set.projIci a x` above
`a` is the positive part of `x - a`, the difference when `x` lies above `a` and zero otherwise. It
is an `[UPSTREAM]` addition to `Mathlib.Algebra.Order.Interval.Set.Group`.
-/

@[expose] public section

namespace Set

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem coe_projIci_sub (a x : α) : (projIci a x : α) - a = (x - a)⁺ := by
  rw [coe_projIci, posPart_def, ← max_sub_sub_right, sub_self, max_comm]

end Set
