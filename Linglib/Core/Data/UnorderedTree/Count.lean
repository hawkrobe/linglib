/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.UnorderedTree.Leaves

/-!
# Size measures on unordered trees and their forests

## Main definitions

* `UnorderedTree.numEdges`: the edge count `numNodes - 1` of a rooted tree.
* `Forest.numNodes`, `Forest.numEdges`: the forest totals.

## Main results

* `Forest.numNodes_eq_card_add_numEdges`: Euler's relation `#V = b₀ + #E` for forests, with
  `Multiset.card` the component count.
* `UnorderedTree.countP_leaves_le_numEdges`: counted leaves are among the non-root vertices
  whenever some vertex is uncounted.
-/

namespace UnorderedTree

variable {α : Type*}

/-- The number of edges of a rooted tree, `numNodes - 1`: every vertex except the root
    has exactly one parent edge. -/
def numEdges (t : UnorderedTree α) : ℕ := t.numNodes - 1

@[simp] theorem numEdges_leaf (a : α) : (leaf a : UnorderedTree α).numEdges = 0 := rfl

theorem numEdges_eq_numNodes_sub_one (t : UnorderedTree α) : t.numEdges = t.numNodes - 1 := rfl

/-- Euler's relation for a rooted tree: `#V = 1 + #E`. -/
theorem numEdges_add_one (t : UnorderedTree α) : t.numEdges + 1 = t.numNodes :=
  Nat.succ_pred_eq_of_pos t.numNodes_pos

/-- The edges of a node are the root-to-child edges plus each child's own: the total
    vertex count of the children. -/
theorem numEdges_node (a : α) (F : Multiset (UnorderedTree α)) :
    (node a F).numEdges = (F.map numNodes).sum := by
  simp [numEdges]

/-- Adjoining a root above a pair of trees adds two edges. -/
theorem numEdges_node_pair (a : α) (l r : UnorderedTree α) :
    (node a {l, r}).numEdges = l.numEdges + r.numEdges + 2 := by
  rw [numEdges_node]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, ← numEdges_add_one]
  omega

/-- Adjoining a root above a pair of trees adds one vertex. -/
theorem numNodes_node_pair (a : α) (l r : UnorderedTree α) :
    (node a {l, r}).numNodes = l.numNodes + r.numNodes + 1 := by
  rw [numNodes_node]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]

/-- Counted leaves are among the non-root vertices whenever some vertex is uncounted. -/
theorem countP_leaves_le_numEdges (p : α → Prop) [DecidablePred p] (t : UnorderedTree α)
    (h : t.leaves.countP p < t.numNodes) : t.leaves.countP p ≤ t.numEdges :=
  Nat.le_sub_one_of_lt h

end UnorderedTree

/-! ### Forest measures -/

namespace Forest

variable {α : Type*}

/-- The total vertex count of a forest. -/
def numNodes (F : Multiset (UnorderedTree α)) : ℕ := (F.map UnorderedTree.numNodes).sum

@[simp] theorem numNodes_zero : numNodes (0 : Multiset (UnorderedTree α)) = 0 := rfl
@[simp] theorem numNodes_cons (T : UnorderedTree α) (F : Multiset (UnorderedTree α)) :
    numNodes (T ::ₘ F) = T.numNodes + numNodes F := by
  simp only [numNodes, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem numNodes_singleton (T : UnorderedTree α) :
    numNodes ({T} : Multiset (UnorderedTree α)) = T.numNodes := by
  simp only [numNodes, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem numNodes_add (F G : Multiset (UnorderedTree α)) :
    numNodes (F + G) = numNodes F + numNodes G := by
  simp only [numNodes, Multiset.map_add, Multiset.sum_add]

/-- The total edge count of a forest. -/
def numEdges (F : Multiset (UnorderedTree α)) : ℕ := (F.map UnorderedTree.numEdges).sum

@[simp] theorem numEdges_zero : numEdges (0 : Multiset (UnorderedTree α)) = 0 := rfl
@[simp] theorem numEdges_cons (T : UnorderedTree α) (F : Multiset (UnorderedTree α)) :
    numEdges (T ::ₘ F) = T.numEdges + numEdges F := by
  simp only [numEdges, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem numEdges_singleton (T : UnorderedTree α) :
    numEdges ({T} : Multiset (UnorderedTree α)) = T.numEdges := by
  simp only [numEdges, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem numEdges_add (F G : Multiset (UnorderedTree α)) :
    numEdges (F + G) = numEdges F + numEdges G := by
  simp only [numEdges, Multiset.map_add, Multiset.sum_add]

/-- Euler's relation for forests: `#V = b₀ + #E`, with `Multiset.card` the number of
    component trees. -/
theorem numNodes_eq_card_add_numEdges (F : Multiset (UnorderedTree α)) :
    numNodes F = Multiset.card F + numEdges F := by
  induction F using Multiset.induction with
  | empty => rfl
  | cons T F ih =>
    simp only [numNodes_cons, numEdges_cons, Multiset.card_cons, ih,
      ← UnorderedTree.numEdges_add_one T]
    omega

end Forest
