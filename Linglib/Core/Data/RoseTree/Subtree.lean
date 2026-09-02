/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Nonplanar

/-!
# Subtrees of nonplanar trees

`Nonplanar.subtrees t` is the multiset of all subtrees of `t`, the root included, one per vertex,
so its cardinality is `t.numNodes`. It is defined on planar representatives and descends to the
quotient because a permutation of children permutes the subtree multiset.

## Main definitions

* `RoseTree.Nonplanar.subtrees`

## Main results

* `RoseTree.Nonplanar.card_subtrees`: one subtree per vertex.
* `RoseTree.Nonplanar.mem_subtrees_node_pair`: membership at a binary node.
-/

namespace RoseTree

variable {α : Type*}

mutual
/-- The nonplanar subtrees of a planar tree, root included. -/
def nonplanarSubtrees : RoseTree α → Multiset (Nonplanar α)
  | .node a cs => Nonplanar.mk (.node a cs) ::ₘ nonplanarSubtreesList cs
/-- The nonplanar subtrees of a list of trees. -/
def nonplanarSubtreesList : List (RoseTree α) → Multiset (Nonplanar α)
  | []      => 0
  | c :: cs => nonplanarSubtrees c + nonplanarSubtreesList cs
end

mutual
theorem nonplanarSubtrees_perm : ∀ {t s : RoseTree α}, Perm t s →
    nonplanarSubtrees t = nonplanarSubtrees s
  | _, _, .node h => by
    simp only [nonplanarSubtrees]
    rw [Nonplanar.mk_eq_mk_iff.mpr (Perm.node h), nonplanarSubtreesList_permList h]
  | _, _, .trans h₁ h₂ => (nonplanarSubtrees_perm h₁).trans (nonplanarSubtrees_perm h₂)

theorem nonplanarSubtreesList_permList : ∀ {cs ds : List (RoseTree α)},
    PermList cs ds → nonplanarSubtreesList cs = nonplanarSubtreesList ds
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [nonplanarSubtreesList, nonplanarSubtrees_perm h, nonplanarSubtreesList_permList hs]
  | _, _, .swap _ _ _ => by simp only [nonplanarSubtreesList]; rw [add_left_comm]
  | _, _, .trans h₁ h₂ =>
    (nonplanarSubtreesList_permList h₁).trans (nonplanarSubtreesList_permList h₂)
end

mutual
theorem card_nonplanarSubtrees (p : RoseTree α) :
    (nonplanarSubtrees p).card = p.numNodes := by
  obtain ⟨a, cs⟩ := p
  rw [nonplanarSubtrees, Multiset.card_cons, card_nonplanarSubtreesList, numNodes_node]; omega
theorem card_nonplanarSubtreesList (cs : List (RoseTree α)) :
    (nonplanarSubtreesList cs).card = (cs.map numNodes).sum := by
  match cs with
  | [] => rfl
  | c :: cs => rw [nonplanarSubtreesList, Multiset.card_add, card_nonplanarSubtrees,
                   card_nonplanarSubtreesList, List.map_cons, List.sum_cons]
end

namespace Nonplanar

/-- All subtrees of a nonplanar tree, root included. -/
def subtrees : Nonplanar α → Multiset (Nonplanar α) :=
  lift nonplanarSubtrees fun _ _ h => nonplanarSubtrees_perm h

@[simp] theorem subtrees_mk (t : RoseTree α) : subtrees (mk t) = nonplanarSubtrees t := rfl

theorem subtrees_leaf (a : α) : subtrees (leaf a) = {leaf a} := by
  show nonplanarSubtrees (RoseTree.leaf a) = _
  simp only [RoseTree.leaf, nonplanarSubtrees, nonplanarSubtreesList]
  rfl

theorem subtrees_node_pair (a : α) (l r : Nonplanar α) :
    subtrees (node a {l, r}) = node a {l, r} ::ₘ (subtrees l + subtrees r) := by
  refine inductionOn₂ l r fun pl pr => ?_
  rw [node_pair_mk]
  simp only [subtrees_mk, nonplanarSubtrees, nonplanarSubtreesList, add_zero]

@[simp] theorem mem_subtrees_leaf {m : Nonplanar α} {a : α} :
    m ∈ subtrees (leaf a) ↔ m = leaf a := by
  rw [subtrees_leaf, Multiset.mem_singleton]

@[simp] theorem mem_subtrees_node_pair {m : Nonplanar α} {a : α} {l r : Nonplanar α} :
    m ∈ subtrees (node a {l, r}) ↔ m = node a {l, r} ∨ m ∈ subtrees l ∨ m ∈ subtrees r := by
  rw [subtrees_node_pair, Multiset.mem_cons, Multiset.mem_add]

theorem self_mem_subtrees (t : Nonplanar α) : t ∈ subtrees t := by
  refine Quotient.inductionOn t fun p => ?_
  obtain ⟨a, cs⟩ := p
  show mk (RoseTree.node a cs) ∈ nonplanarSubtrees (RoseTree.node a cs)
  rw [nonplanarSubtrees]; exact Multiset.mem_cons_self _ _

/-- One subtree per vertex. -/
theorem card_subtrees (t : Nonplanar α) : (subtrees t).card = t.numNodes :=
  Quotient.inductionOn t card_nonplanarSubtrees

end Nonplanar

end RoseTree
