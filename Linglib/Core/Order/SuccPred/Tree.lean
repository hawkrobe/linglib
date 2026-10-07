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
public import Mathlib.Data.List.Iterate
public import Mathlib.Data.Fintype.Card

/-!
# Rooted trees

`[UPSTREAM]` candidate for `Mathlib/Order/SuccPred/Tree.lean`, which represents a rooted tree
by its ancestorship order: a partial order with a bottom, predecessors, and archimedean
descent. This file adds two facts about such orders, and builds the order from a parent map.

Subtrees: the elements above incomparable nodes are disjoint, `disjoint_Ici_of_incompRel`,
since the elements below any node form a chain (`le_total_of_directed`); `RootedTree` states
this for the subtrees under atoms alone.

Meets: with a bottom, binary meets exist, `a ⊓ b` being the first `pred`-iterate of `a` that
lies below `b`. `RootedTree` asks for `SemilatticeInf` as a field; on orders with decidable `≤`
it is derivable.

Parent maps: a `ParentTree` is a map sending each element to its parent, the root to itself,
along which every element reaches the root. Its ancestorship order, `a ≤ b` when `a` is an
iterated parent of `b`, has the root as bottom and the parent as predecessor, and on a finite
type `≤` is decided by walking up from `b`.
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

/-- Binary meets come from archimedean descent: `a ⊓ b` is the first
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

/-! ### Trees from parent maps -/

/-- A `ParentTree` presents a rooted tree by its parent map: the root is its own parent, and every
element reaches the root by iterating the parent map. -/
structure ParentTree (α : Type*) where
  /-- The parent of an element, the root being its own parent. -/
  parent : α → α
  /-- The root. -/
  root : α
  parent_root : parent root = root
  exists_iterate_eq_root (a : α) : ∃ n, parent^[n] a = root

namespace ParentTree

variable {α : Type*} (T : ParentTree α)

theorem iterate_root (n : ℕ) : T.parent^[n] T.root = T.root :=
  Function.iterate_fixed T.parent_root n

variable {T} in
/-- An element that a positive iterate of the parent map fixes is the root. -/
theorem eq_root_of_iterate_eq {a : α} {k : ℕ} (hk : 0 < k) (h : T.parent^[k] a = a) :
    a = T.root := by
  obtain ⟨n, hn⟩ := T.exists_iterate_eq_root a
  have hmul : ∀ j, T.parent^[k * j] a = a := fun j ↦ by
    induction j with
    | zero => rfl
    | succ j ih => rw [Nat.mul_succ, Function.iterate_add_apply, h, ih]
  rw [← hmul n, ← Nat.sub_add_cancel (Nat.le_mul_of_pos_left n hk), Function.iterate_add_apply,
    hn, T.iterate_root]

/-- In the ancestorship order `a ≤ b` when `a` is an iterated parent of `b`. -/
abbrev partialOrder : PartialOrder α where
  le a b := ∃ n, T.parent^[n] b = a
  le_refl _ := ⟨0, rfl⟩
  le_trans _ _ _ := fun ⟨m, hm⟩ ⟨n, hn⟩ ↦ ⟨m + n, by rw [Function.iterate_add_apply, hn, hm]⟩
  le_antisymm a b := fun ⟨m, hm⟩ ⟨n, hn⟩ ↦ by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact hm.symm
    · have hb := eq_root_of_iterate_eq (T := T) (k := n + m) (by omega)
        (by rw [Function.iterate_add_apply, hm, hn])
      rw [← hm, hb, T.iterate_root]

/-- The root is the bottom of the ancestorship order. -/
abbrev orderBot : @OrderBot α T.partialOrder.toLE :=
  letI := T.partialOrder
  { bot := T.root
    bot_le := T.exists_iterate_eq_root }

/-- The parent is the predecessor in the ancestorship order. -/
abbrev predOrder : @PredOrder α T.partialOrder.toPreorder :=
  letI := T.partialOrder
  { pred := T.parent
    pred_le _ := ⟨1, rfl⟩
    min_of_le_pred := fun {a} ⟨n, h⟩ b ⟨k, hk⟩ ↦ by
      have ha := eq_root_of_iterate_eq (T := T) (k := n + 1) (by omega)
        (by rwa [Function.iterate_succ_apply])
      exact ⟨0, by rw [← hk, ha, T.iterate_root, Function.iterate_zero_apply]⟩
    le_pred_of_lt := fun {a b} ⟨⟨n, h⟩, hba⟩ ↦ by
      rcases n with _ | n
      · exact absurd ⟨0, h.symm⟩ hba
      · exact ⟨n, by rwa [← Function.iterate_succ_apply]⟩ }

theorem isPredArchimedean :
    @IsPredArchimedean α T.partialOrder.toPreorder T.predOrder :=
  letI := T.partialOrder
  letI := T.predOrder
  ⟨fun h ↦ h⟩

/-- On a finite type an iterated parent is reached in fewer steps than there are elements. -/
theorem exists_lt_card_of_iterate_eq [Fintype α] {a b : α} {n : ℕ} (h : T.parent^[n] b = a) :
    ∃ m < Fintype.card α, T.parent^[m] b = a := by
  classical
  let N := Nat.find (T.exists_iterate_eq_root b)
  have hN : T.parent^[N] b = T.root := Nat.find_spec (T.exists_iterate_eq_root b)
  have hinj : Function.Injective fun i : Fin (N + 1) ↦ T.parent^[i] b := by
    intro i j hij
    by_contra hne
    wlog hlt : (i : ℕ) < j generalizing i j
    · exact this hij.symm (Ne.symm hne) (by omega)
    have hroot : T.parent^[i] b = T.root := eq_root_of_iterate_eq (T := T)
      (k := j - i) (by omega) (by
        simp only at hij
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, ← hij])
    exact Nat.find_min (T.exists_iterate_eq_root b) (by omega : (i : ℕ) < N) hroot
  have hcard : N + 1 ≤ Fintype.card α := by
    simpa using Fintype.card_le_of_injective _ hinj
  rcases le_or_gt n N with hn | hn
  · exact ⟨n, by omega, h⟩
  · refine ⟨N, by omega, ?_⟩
    rw [← h, hN, ← Nat.sub_add_cancel hn.le, Function.iterate_add_apply, hN, T.iterate_root]

/-- On a finite type `a ≤ b` is decided by walking up from `b`. -/
abbrev decidableLE [Fintype α] [DecidableEq α] : @DecidableLE α T.partialOrder.toLE :=
  fun a b ↦ decidable_of_iff (a ∈ List.iterate T.parent b (Fintype.card α)) <| by
    rw [List.mem_iterate]
    exact ⟨fun ⟨m, _, h⟩ ↦ ⟨m, h.symm⟩, fun ⟨_, h⟩ ↦
      let ⟨m, hm, h'⟩ := T.exists_lt_card_of_iterate_eq h; ⟨m, hm, h'.symm⟩⟩

end ParentTree
