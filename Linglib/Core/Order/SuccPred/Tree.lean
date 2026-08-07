/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Nat.Find

/-!
# Meets in bounded pred-archimedean orders

`[UPSTREAM]` candidate for `Mathlib/Order/SuccPred/Tree.lean`: in a
partial order with a bottom, predecessors, and archimedean descent —
the unbundled data of a rooted tree — binary meets exist: `a ⊓ b` is
the first `pred`-iterate of `a` that lies below `b`. `RootedTree`
currently asks for `SemilatticeInf` as a field; on orders with
decidable `≤` it is derivable.
-/

namespace IsPredArchimedean

variable {α : Type*} [PartialOrder α] [PredOrder α] [IsPredArchimedean α]
  [OrderBot α]

/-- Some `pred`-iterate of `a` lies below `b`: descend all the way
    to `⊥`. -/
theorem exists_pred_iterate_le (a b : α) : ∃ i, Order.pred^[i] a ≤ b :=
  ((bot_le (a := a)).exists_pred_iterate).imp λ _ h => (le_of_eq h).trans bot_le

/-- Binary meets from archimedean descent: `a ⊓ b` is the first
    `pred`-iterate of `a` below `b`. Not an instance: a type may
    already carry a `SemilatticeInf` that this construction need not
    match definitionally. -/
@[reducible] def semilatticeInf [DecidableRel ((· ≤ ·) : α → α → Prop)] :
    SemilatticeInf α where
  inf a b := Order.pred^[Nat.find (exists_pred_iterate_le a b)] a
  inf_le_left a b := Order.pred_iterate_le _ _
  inf_le_right a b := Nat.find_spec (exists_pred_iterate_le a b)
  le_inf c a b hca hcb := by
    obtain ⟨j, hj⟩ := hca.exists_pred_iterate
    have hfind : Nat.find (exists_pred_iterate_le a b) ≤ j :=
      Nat.find_min' _ (hj ▸ hcb)
    calc c = Order.pred^[j] a := hj.symm
      _ = Order.pred^[j - Nat.find (exists_pred_iterate_le a b)]
            (Order.pred^[Nat.find (exists_pred_iterate_le a b)] a) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hfind]
      _ ≤ _ := Order.pred_iterate_le _ _

end IsPredArchimedean
