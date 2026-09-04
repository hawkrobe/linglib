/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Subtrees of nonplanar trees

`UnorderedTree.subtrees t` is the multiset of all subtrees of `t`, the root included, one per
vertex, so its cardinality is `t.numNodes`. It is defined on planar representatives and descends to
the quotient because a permutation of children permutes the subtree multiset.

## Main definitions

* `UnorderedTree.subtrees`

## Main results

* `UnorderedTree.card_subtrees`: one subtree per vertex.
* `UnorderedTree.mem_subtrees_node_pair`: membership at a binary node.
-/

namespace RoseTree

variable {α : Type*}

mutual
/-- The nonplanar subtrees of a planar tree, root included. -/
def unorderedSubtrees : RoseTree α → Multiset (UnorderedTree α)
  | .node a cs => UnorderedTree.mk (.node a cs) ::ₘ unorderedSubtreesList cs
/-- The nonplanar subtrees of a list of trees. -/
def unorderedSubtreesList : List (RoseTree α) → Multiset (UnorderedTree α)
  | []      => 0
  | c :: cs => unorderedSubtrees c + unorderedSubtreesList cs
end

mutual
theorem unorderedSubtrees_perm : ∀ {t s : RoseTree α}, Perm t s →
    unorderedSubtrees t = unorderedSubtrees s
  | _, _, .node h => by
    simp only [unorderedSubtrees]
    rw [UnorderedTree.mk_eq_mk_iff.mpr (Perm.node h), unorderedSubtreesList_permList h]
  | _, _, .trans h₁ h₂ => (unorderedSubtrees_perm h₁).trans (unorderedSubtrees_perm h₂)

theorem unorderedSubtreesList_permList : ∀ {cs ds : List (RoseTree α)},
    PermList cs ds → unorderedSubtreesList cs = unorderedSubtreesList ds
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [unorderedSubtreesList, unorderedSubtrees_perm h, unorderedSubtreesList_permList hs]
  | _, _, .swap _ _ _ => by simp only [unorderedSubtreesList]; rw [add_left_comm]
  | _, _, .trans h₁ h₂ =>
    (unorderedSubtreesList_permList h₁).trans (unorderedSubtreesList_permList h₂)
end

mutual
theorem card_unorderedSubtrees (p : RoseTree α) :
    (unorderedSubtrees p).card = p.numNodes := by
  obtain ⟨a, cs⟩ := p
  rw [unorderedSubtrees, Multiset.card_cons, card_unorderedSubtreesList, numNodes_node]; omega
theorem card_unorderedSubtreesList (cs : List (RoseTree α)) :
    (unorderedSubtreesList cs).card = (cs.map numNodes).sum := by
  match cs with
  | [] => rfl
  | c :: cs => rw [unorderedSubtreesList, Multiset.card_add, card_unorderedSubtrees,
                   card_unorderedSubtreesList, List.map_cons, List.sum_cons]
end

end RoseTree

open RoseTree

namespace UnorderedTree

variable {α : Type*}

/-- All subtrees of a nonplanar tree, root included. -/
def subtrees : UnorderedTree α → Multiset (UnorderedTree α) :=
  lift unorderedSubtrees fun _ _ h => unorderedSubtrees_perm h

@[simp] theorem subtrees_mk (t : RoseTree α) : subtrees (mk t) = unorderedSubtrees t := rfl

theorem subtrees_leaf (a : α) : subtrees (leaf a) = {leaf a} := by
  show unorderedSubtrees (RoseTree.leaf a) = _
  simp only [RoseTree.leaf, unorderedSubtrees, unorderedSubtreesList]
  rfl

theorem subtrees_node_pair (a : α) (l r : UnorderedTree α) :
    subtrees (node a {l, r}) = node a {l, r} ::ₘ (subtrees l + subtrees r) := by
  refine inductionOn₂ l r fun pl pr => ?_
  rw [node_pair_mk]
  simp only [subtrees_mk, unorderedSubtrees, unorderedSubtreesList, add_zero]

@[simp] theorem mem_subtrees_leaf {m : UnorderedTree α} {a : α} :
    m ∈ subtrees (leaf a) ↔ m = leaf a := by
  rw [subtrees_leaf, Multiset.mem_singleton]

@[simp] theorem mem_subtrees_node_pair {m : UnorderedTree α} {a : α} {l r : UnorderedTree α} :
    m ∈ subtrees (node a {l, r}) ↔ m = node a {l, r} ∨ m ∈ subtrees l ∨ m ∈ subtrees r := by
  rw [subtrees_node_pair, Multiset.mem_cons, Multiset.mem_add]

theorem self_mem_subtrees (t : UnorderedTree α) : t ∈ subtrees t := by
  refine Quotient.inductionOn t fun p => ?_
  obtain ⟨a, cs⟩ := p
  show mk (RoseTree.node a cs) ∈ unorderedSubtrees (RoseTree.node a cs)
  rw [unorderedSubtrees]; exact Multiset.mem_cons_self _ _

/-- One subtree per vertex. -/
theorem card_subtrees (t : UnorderedTree α) : (subtrees t).card = t.numNodes :=
  Quotient.inductionOn t card_unorderedSubtrees

end UnorderedTree
