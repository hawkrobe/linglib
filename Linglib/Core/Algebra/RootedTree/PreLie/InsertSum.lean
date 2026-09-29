/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.PreLie.Insertion

/-!
# The grafting pre-Lie product on rooted trees

This file defines the grafting product `T ◁ S` of two rooted trees: the multiset of the trees
obtained by grafting `S` onto one vertex of `T`, that is, by making `S` a new child of that
vertex. Chapoton and Livernet show that this product makes the rooted trees a basis of the free
pre-Lie algebra; Foissy extends it to typed decorated trees.

The product is the one-guest case of the multi-insertion `insertion T gs`, which grafts every
guest of `gs` at once. Everything here is read off that general construction: the
sum-over-vertices formula, the recursion on the root, and the invariance under reordering of
children that descends the product to `UnorderedTree`.

## Main definitions

* `RoseTree.insertSum`: the grafting product on planar trees, with notation `T ◁ S`.
* `UnorderedTree.insertSum`: its descent to nonplanar trees.

## Main results

* `RoseTree.insertSum_eq_map_multiGraft`: `T ◁ S` sums the graftings of `S` over the vertices
  of `T`.
* `RoseTree.insertSum_node`: grafting at the root, or recursively inside one child.
* `RoseTree.card_insertSum`, `UnorderedTree.card_insertSum`: one summand per vertex of `T`.

## Implementation notes

The product of Marcolli, Chomsky and Berwick's insertion Lie algebra is a different operation:
it inserts a binary tree by subdividing an edge of another binary tree, not by grafting at a
vertex.

## References

* [chapoton-livernet-2001]
* [foissy-2021]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace RoseTree

variable {α : Type*}

open Pathed

/-- The grafting product `T ◁ S` is the multiset of trees obtained by grafting `S` as a new
first child of one vertex of `T`. -/
def insertSum (T S : RoseTree α) : Multiset (RoseTree α) :=
  insertion T [S]

@[inherit_doc] scoped infixl:65 " ◁ " => insertSum

/-- `T ◁ S` sums, over the vertices `p` of `T`, the grafting of `S` at `p`. -/
theorem insertSum_eq_map_multiGraft (T S : RoseTree α) :
    T ◁ S = ((vertices T).map fun p => multiGraft T [(p, S)] : Multiset (RoseTree α)) := by
  rw [insertSum, insertion_def, List.length_singleton, listChoices_one, List.map_map]
  rfl

/-- Grafting into a node either adds a child at the root or grafts inside the children. -/
theorem insertSum_node (a : α) (cs : List (RoseTree α)) (S : RoseTree α) :
    node a cs ◁ S = node a (S :: cs) ::ₘ (insertionForest cs [S]).map (node a) := by
  rw [insertSum, insertion_node, show [S].sublists'.revzip = [([], [S]), ([S], [])] from rfl,
    ← Multiset.cons_coe, Multiset.cons_bind, Multiset.coe_singleton, Multiset.singleton_bind,
    insertionForest_nil_guests, Multiset.map_singleton, add_comm, Multiset.singleton_add]
  rfl

@[simp] theorem insertSum_leaf (a : α) (S : RoseTree α) : leaf a ◁ S = {node a [S]} := by
  rw [insertSum_node, insertionForest_empty_host_nonempty_guests, Multiset.map_zero]
  rfl

theorem card_insertSum (T S : RoseTree α) : Multiset.card (T ◁ S) = T.numNodes := by
  rw [insertSum_eq_map_multiGraft, Multiset.coe_card, List.length_map,
    length_vertices_eq_numNodes]

/-- Grafting a leaf onto a two-vertex path adds it at the root or at the old leaf. -/
example : node 0 [leaf 1] ◁ leaf 2 = {node 0 [leaf 2, leaf 1], node 0 [node 1 [leaf 2]]} := by
  decide

end RoseTree

namespace UnorderedTree

variable {α : Type*}

open RoseTree.Pathed

/-- The grafting product on nonplanar trees, descended from `RoseTree.insertSum`. -/
def insertSum : UnorderedTree α → UnorderedTree α → Multiset (UnorderedTree α) :=
  Quotient.lift₂ (fun T S => (RoseTree.insertSum T S).map mk) fun _ _ _ _ h₁ h₂ =>
    (insertion_perm_host h₁ _).trans (insertion_forall₂_perm_guests _ (.cons h₂ .nil))

@[inherit_doc] scoped infixl:65 " ◁ " => UnorderedTree.insertSum

@[simp] theorem mk_insertSum (T S : RoseTree α) :
    mk T ◁ mk S = (RoseTree.insertSum T S).map mk := rfl

theorem card_insertSum (T S : UnorderedTree α) : Multiset.card (T ◁ S) = T.numNodes :=
  Quotient.inductionOn₂ T S fun t s => by
    change Multiset.card (mk t ◁ mk s) = (mk t).numNodes
    rw [mk_insertSum, Multiset.card_map, RoseTree.card_insertSum, numNodes_mk]

end UnorderedTree
