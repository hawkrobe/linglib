/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Nonplanar
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Leaf projections of a rose tree

`leavesWithDepth` collects the leaves of a rose tree as a multiset of
`(label, root-distance)` pairs; `leaves` forgets the depths. Leaf statistics are then
`Multiset` computations — counts are `Multiset.countP`, bounds are inherited from
`Multiset.countP_le_card` — instead of one bespoke fold per statistic.

## Main definitions

* `RoseTree.leavesWithDepth`, `RoseTree.leaves`: the projections, with descents
  `RootedTree.Nonplanar.leavesWithDepth` and `RootedTree.Nonplanar.leaves`.

## Main results

* `RoseTree.card_leavesWithDepth`: the projection has `numLeaves` elements.
* `RoseTree.numLeaves_le_numNodes`: a leaf is a vertex.

`[UPSTREAM]` candidate alongside the `RoseTree` carrier.
-/

namespace RoseTree

variable {α : Type*} (a : α) (c : RoseTree α) (cs : List (RoseTree α))

/-! ### The projections -/

/-- The leaves of a rose tree, each paired with its distance from the root. -/
def leavesWithDepth : RoseTree α → Multiset (α × ℕ) :=
  fold fun a ps =>
    match ps with
    | [] => {(a, 0)}
    | ps => (ps.map (Multiset.map fun p => (p.1, p.2 + 1))).sum

/-- The multiset of leaf labels of a rose tree. -/
def leaves (t : RoseTree α) : Multiset α := t.leavesWithDepth.map Prod.fst

@[simp] theorem leavesWithDepth_leaf : leavesWithDepth (node a []) = {(a, 0)} := rfl

@[simp] theorem leavesWithDepth_node_cons :
    leavesWithDepth (node a (c :: cs))
      = ((c :: cs).map fun t => t.leavesWithDepth.map fun p => (p.1, p.2 + 1)).sum := by
  simp only [leavesWithDepth, fold_node, List.map_cons, List.map_map, Function.comp_def]

@[simp] theorem leaves_leaf : leaves (node a []) = {a} := rfl

private theorem map_list_sum {β γ : Type*} (f : β → γ) (l : List (Multiset β)) :
    Multiset.map f l.sum = (l.map (Multiset.map f)).sum := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [List.sum_cons, Multiset.map_add, ih, List.map_cons]

/-- Depth-forgetting collapses the shift: the leaf labels of a node are the children's
    leaf labels. -/
@[simp] theorem leaves_node_cons :
    leaves (node a (c :: cs)) = ((c :: cs).map leaves).sum := by
  rw [leaves, leavesWithDepth_node_cons, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show (t.leavesWithDepth.map fun p => (p.1, p.2 + 1)).map Prod.fst = _
  rw [Multiset.map_map]
  rfl

/-! ### Cardinality -/

/-- The projection has one element per leaf. -/
theorem card_leavesWithDepth (t : RoseTree α) :
    Multiset.card t.leavesWithDepth = t.numLeaves := by
  induction t with
  | node a cs ih =>
    rcases cs with _ | ⟨c, cs⟩
    · rfl
    · rw [leavesWithDepth_node_cons, numLeaves_node]
      have hsum : ∀ ds : List (RoseTree α), (∀ d ∈ ds, Multiset.card d.leavesWithDepth
            = d.numLeaves) →
          Multiset.card ((ds.map fun t => t.leavesWithDepth.map fun p => (p.1, p.2 + 1)).sum)
            = (ds.map numLeaves).sum := by
        intro ds hds
        induction ds with
        | nil => rfl
        | cons d ds ihd =>
          simp only [List.map_cons, List.sum_cons, Multiset.card_add, Multiset.card_map]
          rw [hds d List.mem_cons_self, ihd fun x hx => hds x (List.mem_cons_of_mem _ hx)]
      rw [hsum (c :: cs) ih]
      have : 0 < ((c :: cs).map numLeaves).sum := by
        simp only [List.map_cons, List.sum_cons]
        have := numLeaves_pos c
        omega
      omega

/-- The number of leaf labels is the number of leaves. -/
theorem card_leaves (t : RoseTree α) : Multiset.card t.leaves = t.numLeaves := by
  rw [leaves, Multiset.card_map, card_leavesWithDepth]

/-- A leaf is a vertex. -/
theorem numLeaves_le_numNodes (t : RoseTree α) : t.numLeaves ≤ t.numNodes := by
  induction t with
  | node a cs ih =>
    rw [numLeaves_node, numNodes_node]
    have := List.sum_le_sum (f := numLeaves) (g := numNodes) ih
    omega

/-! ### `Perm` invariance -/

/-- `leavesWithDepth` is a `Perm`-invariant: the fold algebra reads its arguments only
    through a nil test and a sum. -/
theorem leavesWithDepth_perm {t s : RoseTree α} (h : Perm t s) :
    t.leavesWithDepth = s.leavesWithDepth := by
  refine fold_perm (fun v l₁ l₂ h' => ?_) h
  cases l₁ with
  | nil => rw [← h'.nil_eq]
  | cons x xs =>
    cases l₂ with
    | nil => exact absurd h'.eq_nil (by simp)
    | cons y ys => exact (h'.map (Multiset.map fun p : α × ℕ => (p.1, p.2 + 1))).sum_eq

/-- `leaves` is a `Perm`-invariant. -/
theorem leaves_perm {t s : RoseTree α} (h : Perm t s) : t.leaves = s.leaves :=
  congrArg (Multiset.map Prod.fst) (leavesWithDepth_perm h)

end RoseTree

/-! ### Descent to `Nonplanar` -/

namespace RootedTree.Nonplanar

variable {α : Type*} (a : α)

/-- The leaves of a nonplanar tree, each paired with its distance from the root. -/
def leavesWithDepth : Nonplanar α → Multiset (α × ℕ) :=
  Nonplanar.lift RoseTree.leavesWithDepth fun _ _ => RoseTree.leavesWithDepth_perm

@[simp] theorem leavesWithDepth_mk (t : RoseTree α) :
    (mk t).leavesWithDepth = t.leavesWithDepth := rfl

/-- The multiset of leaf labels of a nonplanar tree. -/
def leaves (t : Nonplanar α) : Multiset α := t.leavesWithDepth.map Prod.fst

@[simp] theorem leaves_mk (t : RoseTree α) : (mk t).leaves = t.leaves := rfl

@[simp] theorem leavesWithDepth_leaf :
    (leaf a : Nonplanar α).leavesWithDepth = {(a, 0)} := rfl

@[simp] theorem leaves_leaf : (leaf a : Nonplanar α).leaves = {a} := rfl

/-- The projection has one element per leaf. -/
theorem card_leavesWithDepth (t : Nonplanar α) :
    Multiset.card t.leavesWithDepth = t.numLeaves :=
  Quotient.inductionOn t fun p => RoseTree.card_leavesWithDepth p

/-- The number of leaf labels is the number of leaves. -/
theorem card_leaves (t : Nonplanar α) : Multiset.card t.leaves = t.numLeaves := by
  rw [leaves, Multiset.card_map, card_leavesWithDepth]

/-- A leaf is a vertex. -/
theorem numLeaves_le_numNodes (t : Nonplanar α) : t.numLeaves ≤ t.numNodes :=
  Quotient.inductionOn t fun p => RoseTree.numLeaves_le_numNodes p

end RootedTree.Nonplanar
