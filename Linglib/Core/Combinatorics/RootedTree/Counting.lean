/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Linglib.Core.Data.RoseTree.Leaves

/-!
# Size measures on rooted nonplanar trees and their forests

## Main definitions

* `RoseTree.leafCountP` / `RoseTree.leafDepthSumP` (with `Nonplanar` descents): leaf
  statistics by predicate, as `Multiset.countP`-computations over the leaf projection.
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

/-- The sum of root-distances of the leaves whose label satisfies `p`. -/
def leafDepthSumP (t : RoseTree α) : ℕ :=
  (t.leavesWithDepth.map fun q => if p q.1 then q.2 else 0).sum

private theorem countP_list_sum (l : List (Multiset γ)) : l.sum.countP q = (l.map fun m => m.countP q).sum := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [List.sum_cons, Multiset.countP_add, ih, List.map_cons]

private theorem sum_map_list_sum (g : γ → ℕ) (l : List (Multiset γ)) :
    (l.sum.map g).sum = (l.map fun m => (m.map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [List.sum_cons, Multiset.map_add, Multiset.sum_add, ih, List.map_cons]

private theorem sum_map_ite_one (m : Multiset γ) : (m.map fun x => if q x then 1 else 0).sum = m.countP q := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons x m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, ih]
    split_ifs <;> omega

private theorem sum_map_le_sum_map (f g : γ → ℕ) (l : List γ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x List.mem_cons_self
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

private theorem leafCountP_eq_countP_leavesWithDepth
    (t : RoseTree α) : leafCountP p t = t.leavesWithDepth.countP fun q => p q.1 := by
  rw [leafCountP, leaves, Multiset.countP_map]
  exact (Multiset.countP_eq_card_filter _ _).symm

@[simp] theorem leafCountP_leaf (a : α) :
    leafCountP p (node a []) = if p a then 1 else 0 := by
  rw [leafCountP, leaves_leaf]
  show Multiset.countP p (a ::ₘ 0) = _
  rw [Multiset.countP_cons, Multiset.countP_zero]
  simp

@[simp] theorem leafCountP_node_cons (a : α)
    (c : RoseTree α) (cs : List (RoseTree α)) :
    leafCountP p (node a (c :: cs)) = ((c :: cs).map (leafCountP p)).sum := by
  rw [leafCountP, leaves_node_cons, countP_list_sum, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun t _ => rfl)

/-- On a non-leaf node the count is the children's total, for any root label. -/
theorem leafCountP_node_of_ne_nil (a : α)
    (cs : List (RoseTree α)) (h : cs ≠ []) :
    leafCountP p (node a cs) = (cs.map (leafCountP p)).sum := by
  rcases cs with _ | ⟨c, cs⟩
  · exact absurd rfl h
  · simp

/-- A root failing `p` contributes nothing, for any child list. -/
theorem leafCountP_node_of_not (a : α)
    (cs : List (RoseTree α)) (h : ¬p a) :
    leafCountP p (node a cs) = (cs.map (leafCountP p)).sum := by
  rcases cs with _ | ⟨c, cs⟩
  · simp [h]
  · simp

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

@[simp] theorem leafDepthSumP_leaf (a : α) :
    leafDepthSumP p (node a []) = 0 := by
  simp [leafDepthSumP]

/-- Each child contributes its own depth-weighted count plus one per counted leaf it
    carries (the extra edge from the node to the child). -/
@[simp] theorem leafDepthSumP_node (a : α)
    (cs : List (RoseTree α)) :
    leafDepthSumP p (node a cs)
      = (cs.map fun c => leafDepthSumP p c + leafCountP p c).sum := by
  rcases cs with _ | ⟨c, cs⟩
  · simp [leafDepthSumP]
  · rw [leafDepthSumP, leavesWithDepth_node_cons, sum_map_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    show ((t.leavesWithDepth.map fun q => (q.1, q.2 + 1)).map
        fun q => if p q.1 then q.2 else 0).sum = _
    rw [Multiset.map_map]
    have hsplit : ((fun q : α × ℕ => if p q.1 then q.2 else 0)
          ∘ fun q : α × ℕ => (q.1, q.2 + 1))
        = fun q : α × ℕ => (if p q.1 then q.2 else 0) + (if p q.1 then 1 else 0) := by
      funext q
      by_cases hq : p q.1 <;> simp [hq]
    rw [hsplit, Multiset.sum_map_add, sum_map_ite_one,
      ← leafCountP_eq_countP_leavesWithDepth]
    rfl

/-- `leafCountP` is a `Perm`-invariant. -/
theorem leafCountP_perm {t s : RoseTree α}
    (h : Perm t s) : leafCountP p t = leafCountP p s := by
  unfold leafCountP
  rw [leaves_perm h]

/-- `leafDepthSumP` is a `Perm`-invariant. -/
theorem leafDepthSumP_perm {t s : RoseTree α}
    (h : Perm t s) : leafDepthSumP p t = leafDepthSumP p s := by
  unfold leafDepthSumP
  rw [leavesWithDepth_perm h]

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
  (Multiset.countP_le_card _ _).trans (by rw [card_leaves]; exact numLeaves_le_numNodes t)

/-- A root failing `p` is an uncounted vertex, so the count is strict. -/
theorem leafCountP_lt_numNodes_of_not (a : α)
    (cs : List (RoseTree α)) (h : ¬p a) :
    leafCountP p (node a cs) < numNodes (node a cs) := by
  rw [leafCountP_node_of_not p a cs h, numNodes_node]
  have := sum_map_le_sum_map (leafCountP p) numNodes cs
    fun c _ => leafCountP_le_numNodes p c
  omega

/-- A root failing `p` puts every counted leaf at depth ≥ 1, so the depth-weighted
    count dominates the plain count. -/
theorem leafCountP_le_leafDepthSumP_of_not (a : α)
    (cs : List (RoseTree α)) (h : ¬p a) :
    leafCountP p (node a cs) ≤ leafDepthSumP p (node a cs) := by
  rw [leafCountP_node_of_not p a cs h, leafDepthSumP_node]
  induction cs with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

end RoseTree

namespace RootedTree

namespace Nonplanar

variable {α : Type*} (p : α → Prop) [DecidablePred p]

/-- The number of edges of a rooted tree, `numNodes - 1`: every vertex except the root
    has exactly one parent edge. -/
def numEdges (t : Nonplanar α) : ℕ := t.numNodes - 1

@[simp] theorem numEdges_leaf (a : α) : (leaf a : Nonplanar α).numEdges = 0 := by
  simp [numEdges]

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
    (leaf a : Nonplanar α).leafCountP p = if p a then 1 else 0 := by
  show (mk (.node a [])).leafCountP p = _
  rw [leafCountP_mk, RoseTree.leafCountP_leaf]

/-- A root failing `p` contributes nothing: the count is the children's total. -/
theorem leafCountP_node_of_not (a : α)
    (F : Multiset (Nonplanar α)) (h : ¬p a) :
    (Nonplanar.node a F).leafCountP p = (F.map (Nonplanar.leafCountP p)).sum := by
  refine Quotient.inductionOn F fun lst => ?_
  show (mk (.node a (lst.map Quotient.out))).leafCountP p = _
  rw [leafCountP_mk, RoseTree.leafCountP_node_of_not p a _ h, List.map_map]
  simp only [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show (mk (Quotient.out t)).leafCountP p = Nonplanar.leafCountP p t
  exact congrArg (Nonplanar.leafCountP p) (Quotient.out_eq t)

/-- The sum of root-distances of the leaves whose label satisfies `p`. -/
def leafDepthSumP : Nonplanar α → ℕ :=
  Nonplanar.lift (RoseTree.leafDepthSumP p) fun _ _ => RoseTree.leafDepthSumP_perm p

@[simp] theorem leafDepthSumP_mk (t : RoseTree α) :
    (mk t).leafDepthSumP p = t.leafDepthSumP p := rfl

@[simp] theorem leafDepthSumP_leaf (a : α) :
    (leaf a : Nonplanar α).leafDepthSumP p = 0 := by
  show (mk (.node a [])).leafDepthSumP p = _
  rw [leafDepthSumP_mk, RoseTree.leafDepthSumP_leaf]

/-- Each child contributes its own depth-weighted count plus one per counted leaf it
    carries. -/
@[simp] theorem leafDepthSumP_node (a : α)
    (F : Multiset (Nonplanar α)) :
    (Nonplanar.node a F).leafDepthSumP p
      = (F.map fun c => c.leafDepthSumP p + c.leafCountP p).sum := by
  refine Quotient.inductionOn F fun lst => ?_
  show (mk (.node a (lst.map Quotient.out))).leafDepthSumP p = _
  rw [leafDepthSumP_mk, RoseTree.leafDepthSumP_node, List.map_map]
  simp only [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show RoseTree.leafDepthSumP p (Quotient.out t) + RoseTree.leafCountP p (Quotient.out t)
      = Nonplanar.leafDepthSumP p t + Nonplanar.leafCountP p t
  congr 1
  · exact congrArg (Nonplanar.leafDepthSumP p) (Quotient.out_eq t)
  · exact congrArg (Nonplanar.leafCountP p) (Quotient.out_eq t)

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
    (h : t.leafCountP p < t.numNodes) : t.leafCountP p ≤ t.numEdges := by
  rw [Nonplanar.numEdges_eq_numNodes_sub_one]
  omega

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
