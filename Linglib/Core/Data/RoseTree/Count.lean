/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Linglib.Core.Data.RoseTree.Leaves

/-!
# Size measures on rooted nonplanar trees and their forests

## Main definitions

* `RoseTree.leafCountP` / `RoseTree.leafDepthsP` / `RoseTree.leafDepthSumP` (with
  `Nonplanar` descents): leaf statistics by predicate over the leaf projection — the
  count is `Multiset.countP`, and the depth statistics are the card and sum of the
  depth multiset (`card_leafDepthsP`).
* `RootedTree.Nonplanar.numEdges`: the edge count `numNodes - 1` of a rooted tree.
* `RootedTree.Forest.numNodes` / `RootedTree.Forest.numEdges`: the forest totals.

## Main results

* `RootedTree.Forest.numNodes_eq_card_add_numEdges`: Euler's relation `#V = b₀ + #E`
  for forests, with `Multiset.card` the component count.
* `RoseTree.leafCountP_le_numNodes`: a counted leaf is a vertex; strict when the root
  is uncounted (`leafCountP_lt_numNodes_of_not`).

`[UPSTREAM]` candidate alongside the `Nonplanar` carrier.
-/

namespace RoseTree

variable {α : Type*} (p : α → Prop) [DecidablePred p]
variable {γ : Type*} (q : γ → Prop) [DecidablePred q]

/-! ### Leaf statistics by predicate -/

/-- The number of leaves whose label satisfies `p`. -/
def leafCountP (t : RoseTree α) : ℕ := t.leaves.countP p

/-- The multiset of root-distances of the leaves whose label satisfies `p`. -/
def leafDepthsP (t : RoseTree α) : Multiset ℕ :=
  (t.leavesWithDepth.filter fun q => p q.1).map Prod.snd

/-- The sum of root-distances of the leaves whose label satisfies `p`. -/
def leafDepthSumP (t : RoseTree α) : ℕ := (leafDepthsP p t).sum

private theorem countP_list_sum (l : List (Multiset γ)) : l.sum.countP q = (l.map fun m => m.countP q).sum := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [List.sum_cons, Multiset.countP_add, ih, List.map_cons]

private theorem filter_list_sum (l : List (Multiset γ)) :
    l.sum.filter q = (l.map (Multiset.filter q)).sum := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [List.sum_cons, Multiset.filter_add, ih, List.map_cons]

private theorem map_list_sum {δ : Type*} (f : γ → δ) (l : List (Multiset γ)) :
    l.sum.map f = (l.map (Multiset.map f)).sum := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [List.sum_cons, Multiset.map_add, ih, List.map_cons]

private theorem sum_list_sum (l : List (Multiset ℕ)) :
    l.sum.sum = (l.map Multiset.sum).sum := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [List.sum_cons, Multiset.sum_add, ih, List.map_cons]

private theorem sum_map_add_one (m : Multiset ℕ) :
    (m.map (· + 1)).sum = m.sum + Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons x m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    omega

@[simp] theorem leafCountP_leaf (a : α) :
    leafCountP p (node a []) = if p a then 1 else 0 := by
  simp only [leafCountP, leaves_leaf, ← Multiset.cons_zero, Multiset.countP_cons,
    Multiset.countP_zero, Nat.zero_add]

@[simp] theorem leafCountP_node_cons (a : α)
    (c : RoseTree α) (cs : List (RoseTree α)) :
    leafCountP p (node a (c :: cs)) = ((c :: cs).map (leafCountP p)).sum := by
  rw [leafCountP, leaves_node_cons, countP_list_sum, List.map_map]; rfl

/-- On a non-leaf node the count is the children's total, for any root label. -/
theorem leafCountP_node_of_ne_nil (a : α)
    (cs : List (RoseTree α)) (h : cs ≠ []) :
    leafCountP p (node a cs) = (cs.map (leafCountP p)).sum := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp

/-- A root failing `p` contributes nothing, for any child list. -/
theorem leafCountP_node_of_not (a : α)
    (cs : List (RoseTree α)) (h : ¬p a) :
    leafCountP p (node a cs) = (cs.map (leafCountP p)).sum := by
  cases cs <;> simp_all

variable {p}

theorem leafCountP_pos {t : RoseTree α} : 0 < leafCountP p t ↔ ∃ a ∈ t.leaves, p a :=
  Multiset.countP_pos

theorem leafCountP_eq_zero {t : RoseTree α} :
    leafCountP p t = 0 ↔ ∀ a ∈ t.leaves, ¬p a :=
  Multiset.countP_eq_zero

/-- The count exhausts the leaves exactly when every leaf label satisfies `p`. -/
theorem leafCountP_eq_numLeaves {t : RoseTree α} :
    leafCountP p t = t.numLeaves ↔ ∀ a ∈ t.leaves, p a := by
  rw [← card_leaves t]
  exact Multiset.countP_eq_card

variable (p)

/-- The counted leaves are exactly the depth entries: `leafCountP` is their number. -/
@[simp] theorem card_leafDepthsP (t : RoseTree α) :
    Multiset.card (leafDepthsP p t) = leafCountP p t := by
  rw [leafDepthsP, Multiset.card_map, leafCountP, leaves, Multiset.countP_map]

@[simp] theorem leafDepthSumP_leaf (a : α) :
    leafDepthSumP p (node a []) = 0 := by
  rw [leafDepthSumP, leafDepthsP, leavesWithDepth_leaf, Multiset.filter_singleton]
  split_ifs <;> rfl

/-- The counted-leaf depths of a node are the children's, each one edge deeper. -/
theorem leafDepthsP_node_cons (a : α) (c : RoseTree α) (cs : List (RoseTree α)) :
    leafDepthsP p (node a (c :: cs))
      = ((c :: cs).map fun t => (leafDepthsP p t).map (· + 1)).sum := by
  rw [leafDepthsP, leavesWithDepth_node_cons, filter_list_sum, map_list_sum,
    List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_def, Multiset.filter_map, Multiset.map_map, leafDepthsP]

/-- Each child contributes its own depth-weighted count plus one per counted leaf it
    carries (the extra edge from the node to the child). -/
@[simp] theorem leafDepthSumP_node (a : α) (cs : List (RoseTree α)) :
    leafDepthSumP p (node a cs)
      = (cs.map fun c => leafDepthSumP p c + leafCountP p c).sum := by
  rcases cs with _ | ⟨c, cs⟩
  · simp
  · rw [leafDepthSumP, leafDepthsP_node_cons, sum_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    show ((leafDepthsP p t).map (· + 1)).sum = _
    rw [sum_map_add_one, card_leafDepthsP]
    rfl

/-- `leafCountP` is a `Perm`-invariant. -/
theorem leafCountP_perm {t s : RoseTree α} (h : Perm t s) :
    leafCountP p t = leafCountP p s :=
  congrArg (Multiset.countP p) (leaves_perm h)

/-- `leafDepthsP` is a `Perm`-invariant. -/
theorem leafDepthsP_perm {t s : RoseTree α} (h : Perm t s) :
    leafDepthsP p t = leafDepthsP p s := by
  unfold leafDepthsP
  rw [leavesWithDepth_perm h]

/-- `leafDepthSumP` is a `Perm`-invariant. -/
theorem leafDepthSumP_perm {t s : RoseTree α} (h : Perm t s) :
    leafDepthSumP p t = leafDepthSumP p s :=
  congrArg Multiset.sum (leafDepthsP_perm p h)

/-- The children's counted leaves are bounded by the node's. -/
theorem sum_map_leafCountP_le_node (a : α)
    (cs : List (RoseTree α)) :
    (cs.map (leafCountP p)).sum ≤ leafCountP p (node a cs) := by
  rcases cs with _ | ⟨c, cs⟩
  · exact Nat.zero_le _
  · exact ge_of_eq (by simp)

/-- A counted leaf is a vertex: `Multiset.countP_le_card` through the leaf projection. -/
theorem leafCountP_le_numNodes (t : RoseTree α) :
    leafCountP p t ≤ t.numNodes :=
  (Multiset.countP_le_card _ _).trans ((card_leaves t).trans_le (numLeaves_le_numNodes t))

/-- A root failing `p` is an uncounted vertex, so the count is strict. -/
theorem leafCountP_lt_numNodes_of_not (a : α)
    (cs : List (RoseTree α)) (h : ¬p a) :
    leafCountP p (node a cs) < numNodes (node a cs) := by
  rw [leafCountP_node_of_not p a cs h, numNodes_node]
  have := List.sum_le_sum (l := cs) (f := leafCountP p) (g := numNodes)
    fun c _ => leafCountP_le_numNodes p c
  omega

/-- A root failing `p` puts every counted leaf at depth ≥ 1, so the depth-weighted
    count dominates the plain count. -/
theorem leafCountP_le_leafDepthSumP_of_not (a : α)
    (cs : List (RoseTree α)) (h : ¬p a) :
    leafCountP p (node a cs) ≤ leafDepthSumP p (node a cs) := by
  rw [leafCountP_node_of_not p a cs h, leafDepthSumP_node]
  exact List.sum_le_sum fun c _ => Nat.le_add_left _ _

end RoseTree

namespace RootedTree

namespace Nonplanar

variable {α : Type*} (p : α → Prop) [DecidablePred p]

/-- The number of edges of a rooted tree, `numNodes - 1`: every vertex except the root
    has exactly one parent edge. -/
def numEdges (t : Nonplanar α) : ℕ := t.numNodes - 1

@[simp] theorem numEdges_leaf (a : α) : (leaf a : Nonplanar α).numEdges = 0 := rfl

theorem numEdges_eq_numNodes_sub_one (t : Nonplanar α) : t.numEdges = t.numNodes - 1 := rfl

/-- Euler's relation for a rooted tree: `#V = 1 + #E`. -/
theorem numEdges_add_one (t : Nonplanar α) : t.numEdges + 1 = t.numNodes :=
  Nat.succ_pred_eq_of_pos t.numNodes_pos

/-- The edges of a node are the root-to-child edges plus each child's own: the total
    vertex count of the children. -/
theorem numEdges_node (a : α) (F : Multiset (Nonplanar α)) :
    (node a F).numEdges = (F.map numNodes).sum := by
  simp [numEdges]

/-- Adjoining a root above a pair of trees adds two edges. -/
theorem numEdges_node_pair (a : α) (l r : Nonplanar α) :
    (node a {l, r}).numEdges = l.numEdges + r.numEdges + 2 := by
  rw [numEdges_node]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, ← numEdges_add_one]
  omega


/-! ### Leaf statistics by predicate, on the quotient -/

/-- The number of leaves whose label satisfies `p`. -/
def leafCountP : Nonplanar α → ℕ :=
  Nonplanar.lift (RoseTree.leafCountP p) fun _ _ => RoseTree.leafCountP_perm p

@[simp] theorem leafCountP_mk (t : RoseTree α) :
    (mk t).leafCountP p = t.leafCountP p := rfl

@[simp] theorem leafCountP_leaf (a : α) :
    (leaf a : Nonplanar α).leafCountP p = if p a then 1 else 0 :=
  RoseTree.leafCountP_leaf p a

/-- A root failing `p` contributes nothing: the count is the children's total. -/
theorem leafCountP_node_of_not (a : α)
    (F : Multiset (Nonplanar α)) (h : ¬p a) :
    (Nonplanar.node a F).leafCountP p = (F.map (Nonplanar.leafCountP p)).sum := by
  induction F using forest_inductionOn with
  | h cs =>
    rw [node_mk_tree_list, leafCountP_mk, RoseTree.leafCountP_node_of_not p a cs h,
      Multiset.map_coe, Multiset.sum_coe, List.map_map]
    rfl

/-- The sum of root-distances of the leaves whose label satisfies `p`. -/
def leafDepthSumP : Nonplanar α → ℕ :=
  Nonplanar.lift (RoseTree.leafDepthSumP p) fun _ _ => RoseTree.leafDepthSumP_perm p

@[simp] theorem leafDepthSumP_mk (t : RoseTree α) :
    (mk t).leafDepthSumP p = t.leafDepthSumP p := rfl

@[simp] theorem leafDepthSumP_leaf (a : α) :
    (leaf a : Nonplanar α).leafDepthSumP p = 0 :=
  RoseTree.leafDepthSumP_leaf p a

/-- Each child contributes its own depth-weighted count plus one per counted leaf it
    carries. -/
@[simp] theorem leafDepthSumP_node (a : α)
    (F : Multiset (Nonplanar α)) :
    (Nonplanar.node a F).leafDepthSumP p
      = (F.map fun c => c.leafDepthSumP p + c.leafCountP p).sum := by
  induction F using forest_inductionOn with
  | h cs =>
    rw [node_mk_tree_list, leafDepthSumP_mk, RoseTree.leafDepthSumP_node,
      Multiset.map_coe, Multiset.sum_coe, List.map_map]
    rfl

/-- A root failing `p` is an uncounted vertex, so the count is strict. -/
theorem leafCountP_lt_numNodes_of_not_root
    (t : Nonplanar α) (h : ¬p t.rootValue) : t.leafCountP p < t.numNodes := by
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : RoseTree α, t = Nonplanar.mk t₀ :=
    ⟨t.out, (Quotient.out_eq t).symm⟩
  rw [Nonplanar.rootValue_mk] at h
  cases t₀ with
  | node x cs =>
    rw [RoseTree.value_node] at h
    rw [Nonplanar.leafCountP_mk, Nonplanar.numNodes_mk]
    exact RoseTree.leafCountP_lt_numNodes_of_not p x cs h

/-- A root failing `p` puts every counted leaf at depth ≥ 1. -/
theorem leafCountP_le_leafDepthSumP_of_not_root
    (t : Nonplanar α) (h : ¬p t.rootValue) : t.leafCountP p ≤ t.leafDepthSumP p := by
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : RoseTree α, t = Nonplanar.mk t₀ :=
    ⟨t.out, (Quotient.out_eq t).symm⟩
  rw [Nonplanar.rootValue_mk] at h
  cases t₀ with
  | node x cs =>
    rw [RoseTree.value_node] at h
    rw [Nonplanar.leafCountP_mk, Nonplanar.leafDepthSumP_mk]
    exact RoseTree.leafCountP_le_leafDepthSumP_of_not p x cs h

/-- Counted leaves are among the non-root vertices whenever some vertex is uncounted. -/
theorem leafCountP_le_numEdges (t : Nonplanar α)
    (h : t.leafCountP p < t.numNodes) : t.leafCountP p ≤ t.numEdges :=
  Nat.le_sub_one_of_lt h

end Nonplanar

/-! ### Forest measures -/

namespace Forest

variable {α : Type*}

/-- The total vertex count of a forest. -/
def numNodes (F : Multiset (Nonplanar α)) : ℕ := (F.map Nonplanar.numNodes).sum

@[simp] theorem numNodes_zero : numNodes (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem numNodes_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    numNodes (T ::ₘ F) = T.numNodes + numNodes F := by
  simp only [numNodes, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem numNodes_singleton (T : Nonplanar α) :
    numNodes ({T} : Multiset (Nonplanar α)) = T.numNodes := by
  simp only [numNodes, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem numNodes_add (F G : Multiset (Nonplanar α)) :
    numNodes (F + G) = numNodes F + numNodes G := by
  simp only [numNodes, Multiset.map_add, Multiset.sum_add]

/-- The total edge count of a forest. -/
def numEdges (F : Multiset (Nonplanar α)) : ℕ := (F.map Nonplanar.numEdges).sum

@[simp] theorem numEdges_zero : numEdges (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem numEdges_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    numEdges (T ::ₘ F) = T.numEdges + numEdges F := by
  simp only [numEdges, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem numEdges_singleton (T : Nonplanar α) :
    numEdges ({T} : Multiset (Nonplanar α)) = T.numEdges := by
  simp only [numEdges, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem numEdges_add (F G : Multiset (Nonplanar α)) :
    numEdges (F + G) = numEdges F + numEdges G := by
  simp only [numEdges, Multiset.map_add, Multiset.sum_add]

/-- Euler's relation for forests: `#V = b₀ + #E`, with `Multiset.card` the number of
    component trees. -/
theorem numNodes_eq_card_add_numEdges (F : Multiset (Nonplanar α)) :
    numNodes F = Multiset.card F + numEdges F := by
  induction F using Multiset.induction with
  | empty => rfl
  | cons T F ih =>
    simp only [numNodes_cons, numEdges_cons, Multiset.card_cons, ih,
      ← Nonplanar.numEdges_add_one T]
    omega

end Forest

end RootedTree
