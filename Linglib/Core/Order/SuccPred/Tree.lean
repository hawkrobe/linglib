/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.EquivFin

/-!
# Rooted trees

`[UPSTREAM]` candidate for `Mathlib/Order/SuccPred/Tree.lean`, which represents a rooted tree
by its ancestorship order: a partial order with a bottom, predecessors, and archimedean
descent. This file adds two things that file lacks.

The tree of a parent map: on a finite type, a map `pred` under which every element reaches
`root` in `Fintype.card α` steps presents a rooted tree, `a ≤ b` when `a` is an iterate of
`pred` from `b`. `PartialOrder.ofPred`, `OrderBot.ofPred`, `PredOrder.ofPred` and
`DecidableLE.ofPred` build the order, its root, its predecessor and its decidability from that
one fact; archimedean descent follows from finiteness.

Meets: in a partial order with a bottom, predecessors, and archimedean descent, binary meets
exist, `a ⊓ b` being the first `pred`-iterate of `a` that lies below `b`. `RootedTree` asks for
`SemilatticeInf` as a field; on orders with decidable `≤` it is derivable.
-/

open Function

section OfPred

variable {α : Type*} [Fintype α] {pred : α → α} {root : α}

/-- The root is a fixed point of the parent map. -/
theorem pred_root_of_iterate_card (hroot : ∀ a, pred^[Fintype.card α] a = root) :
    pred root = root := by
  have h := hroot (pred root)
  rwa [← iterate_succ_apply, iterate_succ_apply', hroot] at h

/-- An element on a cycle of the parent map is the root. -/
theorem eq_root_of_iterate_eq_self (hroot : ∀ a, pred^[Fintype.card α] a = root) {a : α}
    {n : ℕ} (hn : n ≠ 0) (h : pred^[n] a = a) : a = root := by
  have hmul : pred^[n * Fintype.card α] a = a := by
    rw [iterate_mul]; exact iterate_fixed h _
  calc a = pred^[n * Fintype.card α] a := hmul.symm
    _ = pred^[n * Fintype.card α - Fintype.card α] (pred^[Fintype.card α] a) := by
      rw [← iterate_add_apply,
        Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hn))]
    _ = root := by rw [hroot, iterate_fixed (pred_root_of_iterate_card hroot)]

/-- The ancestorship order of a parent map: `a ≤ b` when `a` is an iterate of `pred` from
`b`. -/
@[instance_reducible]
def PartialOrder.ofPred (hroot : ∀ a, pred^[Fintype.card α] a = root) : PartialOrder α where
  le a b := ∃ k, pred^[k] b = a
  le_refl _ := ⟨0, rfl⟩
  le_trans _ _ _ := fun ⟨k, hk⟩ ⟨j, hj⟩ ↦ ⟨k + j, by rw [iterate_add_apply, hj, hk]⟩
  le_antisymm a b := fun ⟨k, hk⟩ ⟨j, hj⟩ ↦ by
    rcases Nat.eq_zero_or_pos (j + k) with h0 | hpos
    · obtain ⟨-, rfl⟩ := Nat.add_eq_zero_iff.1 h0
      exact hk.symm
    · have hb : b = root :=
        eq_root_of_iterate_eq_self hroot hpos.ne' (by rw [iterate_add_apply, hk, hj])
      subst hb
      rw [iterate_fixed (pred_root_of_iterate_card hroot)] at hk
      exact hk.symm

/-- The root as the bottom of the ancestorship order. -/
@[instance_reducible]
def OrderBot.ofPred (hroot : ∀ a, pred^[Fintype.card α] a = root) :
    letI := PartialOrder.ofPred hroot; OrderBot α :=
  letI := PartialOrder.ofPred hroot
  { bot := root, bot_le := fun a ↦ ⟨_, hroot a⟩ }

/-- The parent map as the predecessor of the ancestorship order. -/
@[instance_reducible]
def PredOrder.ofPred (hroot : ∀ a, pred^[Fintype.card α] a = root) :
    letI := PartialOrder.ofPred hroot; PredOrder α :=
  letI := PartialOrder.ofPred hroot
  { pred := pred
    pred_le := fun _ ↦ ⟨1, rfl⟩
    min_of_le_pred := fun {a} ⟨k, hk⟩ ↦ by
      have ha : a = root :=
        eq_root_of_iterate_eq_self hroot k.succ_ne_zero (by rwa [iterate_succ_apply])
      subst ha
      exact fun b _ ↦ ⟨_, hroot b⟩
    le_pred_of_lt := fun {a b} h ↦ by
      obtain ⟨k, hk⟩ := h.le
      cases k with
      | zero => exact absurd hk.symm h.ne
      | succ k => exact ⟨k, by rwa [iterate_succ_apply] at hk⟩ }

/-- Ancestorship is decidable: an ancestor is reached within `Fintype.card α` steps. -/
@[instance_reducible]
def DecidableLE.ofPred [DecidableEq α] (hroot : ∀ a, pred^[Fintype.card α] a = root) :
    letI := PartialOrder.ofPred hroot; DecidableLE α :=
  letI := PartialOrder.ofPred hroot
  fun a b ↦ decidable_of_iff (∃ k < Fintype.card α + 1, pred^[k] b = a) <| by
    constructor
    · rintro ⟨k, -, hk⟩
      exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      rcases Nat.lt_or_ge (Fintype.card α) k with hlt | hle
      · refine ⟨Fintype.card α, Nat.lt_succ_self _, ?_⟩
        rw [hroot, ← hk, ← Nat.sub_add_cancel hlt.le, iterate_add_apply, hroot,
          iterate_fixed (pred_root_of_iterate_card hroot)]
      · exact ⟨k, Nat.lt_succ_of_le hle, hk⟩

end OfPred

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
