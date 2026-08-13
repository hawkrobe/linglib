/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Data.Multiset.Bind

set_option autoImplicit false

/-!
# Sums over multiset cartesian products

`[UPSTREAM]` candidate: the `Multiset` analogue of `Finset.sum_mul_sum`,
absent from mathlib.
-/

namespace Multiset

/-- Sum of a pointwise product over a cartesian product factors as a
    product of sums. -/
theorem sum_map_product_mul {α β M : Type*} [NonUnitalNonAssocSemiring M]
    (s : Multiset α) (t : Multiset β) (f : α → M) (g : β → M) :
    ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum = (s.map f).sum * (t.map g).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih,
        Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    rw [Multiset.map_map,
        show (fun p => f p.1 * g p.2) ∘ (Prod.mk a) = (fun b => f a * g b) from rfl,
        ← Multiset.sum_map_mul_left]

end Multiset
