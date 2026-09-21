/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Comparable
public import Mathlib.Data.Nat.Find

/-!
# Rooted trees

`[UPSTREAM]` candidate for `Mathlib/Order/SuccPred/Tree.lean`, which represents a rooted tree
by its ancestorship order: a partial order with a bottom, predecessors, and archimedean
descent. This file adds two facts about such orders.

Subtrees: the elements above incomparable nodes are disjoint, `disjoint_Ici_of_incompRel`,
since the elements below any node form a chain (`le_total_of_directed`); `RootedTree` states
this for the subtrees under atoms alone.

Meets: with a bottom, binary meets exist, `a ⊓ b` being the first `pred`-iterate of `a` that
lies below `b`. `RootedTree` asks for `SemilatticeInf` as a field; on orders with decidable `≤`
it is derivable.
-/

@[expose] public section

section Subtrees

variable {α : Type*} [Preorder α] [PredOrder α] [IsPredArchimedean α]

/-- The subtrees under incomparable nodes are disjoint. -/
theorem disjoint_Ici_of_incompRel {a b : α} (h : IncompRel (· ≤ ·) a b) :
    Disjoint (Set.Ici a) (Set.Ici b) :=
  Set.disjoint_left.2 fun _ ha hb ↦ (le_total_of_directed ha hb).elim h.2 h.1

end Subtrees

namespace IsPredArchimedean

variable {α : Type*} [PartialOrder α] [PredOrder α] [IsPredArchimedean α]
  [OrderBot α]

/-- Some `pred`-iterate of `a` lies below `b`: descend all the way
    to `⊥`. -/
theorem exists_pred_iterate_le (a b : α) : ∃ i, Order.pred^[i] a ≤ b :=
  ((bot_le (a := a)).exists_pred_iterate).imp fun _ h ↦ (le_of_eq h).trans bot_le

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
