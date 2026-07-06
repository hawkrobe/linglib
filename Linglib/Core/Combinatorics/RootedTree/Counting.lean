/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Linglib.Core.Data.RoseTree.Leaves

/-!
# Size measures on forests of rooted nonplanar trees

For a forest `F : Multiset (Nonplanar α)`: `b₀` counts component trees, `alpha` counts
non-root vertices (equivalently, edges), and `sigma = b₀ + alpha` is the total vertex
count (`sigma_eq_sum_numNodes`) — the forest case of `#V = b₀ + #E`.

## Main definitions

* `RootedTree.Nonplanar.accCount`: the non-root vertex count `numNodes - 1` of a tree.
* `RootedTree.Forest.b₀`: the number of component trees.
* `RootedTree.Forest.alpha`: the total non-root vertex count.
* `RootedTree.Forest.sigma`: `b₀ + alpha`.

## Main results

* `RootedTree.Forest.sigma_eq_sum_numNodes`: `sigma F = (F.map numNodes).sum`.

`[UPSTREAM]` candidate alongside the `Nonplanar` carrier.
-/

namespace RoseTree

variable {α : Type*}

/-! ### Leaf statistics by predicate -/

/-- The number of leaves whose label satisfies `p`. -/
def leafCountP (p : α → Prop) [DecidablePred p] (t : RoseTree α) : ℕ := t.leaves.countP p

/-- The sum of root-distances of the leaves whose label satisfies `p`. -/
def leafDepthSumP (p : α → Prop) [DecidablePred p] (t : RoseTree α) : ℕ :=
  (t.leavesWithDepth.map fun q => if p q.1 then q.2 else 0).sum

private theorem countP_list_sum {γ : Type*} (q : γ → Prop) [DecidablePred q]
    (l : List (Multiset γ)) : l.sum.countP q = (l.map fun m => m.countP q).sum := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [List.sum_cons, Multiset.countP_add, ih, List.map_cons]

private theorem sum_map_list_sum {γ : Type*} (g : γ → ℕ) (l : List (Multiset γ)) :
    (l.sum.map g).sum = (l.map fun m => (m.map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [List.sum_cons, Multiset.map_add, Multiset.sum_add, ih, List.map_cons]

private theorem sum_map_ite_one {γ : Type*} (q : γ → Prop) [DecidablePred q]
    (m : Multiset γ) : (m.map fun x => if q x then 1 else 0).sum = m.countP q := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons x m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, ih]
    split_ifs <;> omega

private theorem sum_map_le_sum_map {γ : Type*} (f g : γ → ℕ) (l : List γ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x List.mem_cons_self
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

private theorem leafCountP_eq_countP_leavesWithDepth (p : α → Prop) [DecidablePred p]
    (t : RoseTree α) : leafCountP p t = t.leavesWithDepth.countP fun q => p q.1 := by
  rw [leafCountP, leaves, Multiset.countP_map]
  exact (Multiset.countP_eq_card_filter _ _).symm

@[simp] theorem leafCountP_leaf (p : α → Prop) [DecidablePred p] (a : α) :
    leafCountP p (node a []) = if p a then 1 else 0 := by
  rw [leafCountP, leaves_leaf]
  show Multiset.countP p (a ::ₘ 0) = _
  rw [Multiset.countP_cons, Multiset.countP_zero]
  simp

@[simp] theorem leafCountP_node_cons (p : α → Prop) [DecidablePred p] (a : α)
    (c : RoseTree α) (cs : List (RoseTree α)) :
    leafCountP p (node a (c :: cs)) = ((c :: cs).map (leafCountP p)).sum := by
  rw [leafCountP, leaves_node_cons, countP_list_sum, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun t _ => rfl)

/-- On a non-leaf node the count is the children's total, for any root label. -/
theorem leafCountP_node_of_ne_nil (p : α → Prop) [DecidablePred p] (a : α)
    (cs : List (RoseTree α)) (h : cs ≠ []) :
    leafCountP p (node a cs) = (cs.map (leafCountP p)).sum := by
  rcases cs with _ | ⟨c, cs⟩
  · exact absurd rfl h
  · simp

/-- A root failing `p` contributes nothing, for any child list. -/
theorem leafCountP_node_of_not (p : α → Prop) [DecidablePred p] (a : α)
    (cs : List (RoseTree α)) (h : ¬p a) :
    leafCountP p (node a cs) = (cs.map (leafCountP p)).sum := by
  rcases cs with _ | ⟨c, cs⟩
  · simp [h]
  · simp

@[simp] theorem leafDepthSumP_leaf (p : α → Prop) [DecidablePred p] (a : α) :
    leafDepthSumP p (node a []) = 0 := by
  simp [leafDepthSumP]

/-- Each child contributes its own depth-weighted count plus one per counted leaf it
    carries (the extra edge from the node to the child). -/
@[simp] theorem leafDepthSumP_node (p : α → Prop) [DecidablePred p] (a : α)
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
theorem leafCountP_perm (p : α → Prop) [DecidablePred p] {t s : RoseTree α}
    (h : Perm t s) : leafCountP p t = leafCountP p s := by
  unfold leafCountP
  rw [leaves_perm h]

/-- `leafDepthSumP` is a `Perm`-invariant. -/
theorem leafDepthSumP_perm (p : α → Prop) [DecidablePred p] {t s : RoseTree α}
    (h : Perm t s) : leafDepthSumP p t = leafDepthSumP p s := by
  unfold leafDepthSumP
  rw [leavesWithDepth_perm h]

/-- The children's counted leaves are bounded by the node's. -/
theorem sum_map_leafCountP_le_node (p : α → Prop) [DecidablePred p] (a : α)
    (cs : List (RoseTree α)) :
    (cs.map (leafCountP p)).sum ≤ leafCountP p (node a cs) := by
  rcases cs with _ | ⟨c, cs⟩
  · exact Nat.zero_le _
  · exact ge_of_eq (by simp)

/-- A counted leaf is a vertex: `Multiset.countP_le_card` through the leaf projection. -/
theorem leafCountP_le_numNodes (p : α → Prop) [DecidablePred p] (t : RoseTree α) :
    leafCountP p t ≤ t.numNodes :=
  (Multiset.countP_le_card _ _).trans (by rw [card_leaves]; exact numLeaves_le_numNodes t)

/-- A root failing `p` is an uncounted vertex, so the count is strict. -/
theorem leafCountP_lt_numNodes_of_not (p : α → Prop) [DecidablePred p] (a : α)
    (cs : List (RoseTree α)) (h : ¬p a) :
    leafCountP p (node a cs) < numNodes (node a cs) := by
  rw [leafCountP_node_of_not p a cs h, numNodes_node]
  have := sum_map_le_sum_map (leafCountP p) numNodes cs
    fun c _ => leafCountP_le_numNodes p c
  omega

/-- A root failing `p` puts every counted leaf at depth ≥ 1, so the depth-weighted
    count dominates the plain count. -/
theorem leafCountP_le_leafDepthSumP_of_not (p : α → Prop) [DecidablePred p] (a : α)
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

variable {α : Type*}

/-- The number of non-root vertices of a rooted tree, `numNodes - 1` (equivalently, its
    edge count). -/
def accCount (t : Nonplanar α) : ℕ := t.numNodes - 1

@[simp] theorem accCount_leaf (a : α) : (leaf a : Nonplanar α).accCount = 0 := by
  simp [accCount]

theorem accCount_eq_numNodes_sub_one (t : Nonplanar α) : t.accCount = t.numNodes - 1 := rfl

/-- `accCount + 1` recovers the vertex count. -/
theorem accCount_add_one (t : Nonplanar α) : t.accCount + 1 = t.numNodes :=
  Nat.succ_pred_eq_of_pos t.numNodes_pos

/-- `accCount` at a node is the total vertex count of the children. -/
theorem accCount_node (a : α) (F : Multiset (Nonplanar α)) :
    (node a F).accCount = (F.map numNodes).sum := by
  simp [accCount]

/-- Adjoining a root above a pair of trees adds two non-root vertices. -/
theorem accCount_node_pair (a : α) (l r : Nonplanar α) :
    (node a {l, r}).accCount = l.accCount + r.accCount + 2 := by
  rw [accCount_node]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, ← accCount_add_one]
  omega


/-! ### Leaf statistics by predicate, on the quotient -/

/-- The number of leaves whose label satisfies `p`. -/
def leafCountP (p : α → Prop) [DecidablePred p] : Nonplanar α → ℕ :=
  Nonplanar.lift (RoseTree.leafCountP p) fun _ _ => RoseTree.leafCountP_perm p

@[simp] theorem leafCountP_mk (p : α → Prop) [DecidablePred p] (t : RoseTree α) :
    (mk t).leafCountP p = t.leafCountP p := rfl

@[simp] theorem leafCountP_leaf (p : α → Prop) [DecidablePred p] (a : α) :
    (leaf a : Nonplanar α).leafCountP p = if p a then 1 else 0 := by
  show (mk (.node a [])).leafCountP p = _
  rw [leafCountP_mk, RoseTree.leafCountP_leaf]

/-- A root failing `p` contributes nothing: the count is the children's total. -/
theorem leafCountP_node_of_not (p : α → Prop) [DecidablePred p] (a : α)
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
def leafDepthSumP (p : α → Prop) [DecidablePred p] : Nonplanar α → ℕ :=
  Nonplanar.lift (RoseTree.leafDepthSumP p) fun _ _ => RoseTree.leafDepthSumP_perm p

@[simp] theorem leafDepthSumP_mk (p : α → Prop) [DecidablePred p] (t : RoseTree α) :
    (mk t).leafDepthSumP p = t.leafDepthSumP p := rfl

@[simp] theorem leafDepthSumP_leaf (p : α → Prop) [DecidablePred p] (a : α) :
    (leaf a : Nonplanar α).leafDepthSumP p = 0 := by
  show (mk (.node a [])).leafDepthSumP p = _
  rw [leafDepthSumP_mk, RoseTree.leafDepthSumP_leaf]

/-- Each child contributes its own depth-weighted count plus one per counted leaf it
    carries. -/
@[simp] theorem leafDepthSumP_node (p : α → Prop) [DecidablePred p] (a : α)
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
theorem leafCountP_lt_numNodes_of_not_root (p : α → Prop) [DecidablePred p]
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
theorem leafCountP_le_leafDepthSumP_of_not_root (p : α → Prop) [DecidablePred p]
    (t : Nonplanar α) (h : ¬p t.rootValue) : t.leafCountP p ≤ t.leafDepthSumP p := by
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : RoseTree α, t = Nonplanar.mk t₀ :=
    ⟨t.out, (Quotient.out_eq t).symm⟩
  rw [Nonplanar.rootValue_mk] at h
  cases t₀ with
  | node x cs =>
    rw [RoseTree.value_node] at h
    rw [Nonplanar.leafCountP_mk, Nonplanar.leafDepthSumP_mk]
    exact RoseTree.leafCountP_le_leafDepthSumP_of_not p x cs h

/-! ### Discounted accessible-term count -/

/-- Non-root vertices, discounting the `p`-leaves. Truncated subtraction covers the
    single-`p`-leaf tree, whose root is its one leaf. -/
def accCountP (p : α → Prop) [DecidablePred p] (t : Nonplanar α) : ℕ :=
  t.accCount - t.leafCountP p

/-- Counted leaves are among the non-root vertices whenever some vertex is uncounted. -/
theorem leafCountP_le_accCount (p : α → Prop) [DecidablePred p] (t : Nonplanar α)
    (h : t.leafCountP p < t.numNodes) : t.leafCountP p ≤ t.accCount := by
  rw [Nonplanar.accCount_eq_numNodes_sub_one]
  omega

/-- Adjoining a root (not counted by `p`) above a pair adds two discounted
    accessible terms. -/
theorem accCountP_node_pair (p : α → Prop) [DecidablePred p] (a : α)
    (l r : Nonplanar α) (hpa : ¬p a)
    (hl : l.leafCountP p < l.numNodes) (hr : r.leafCountP p < r.numNodes) :
    (Nonplanar.node a {l, r}).accCountP p = l.accCountP p + r.accCountP p + 2 := by
  have hw := Nonplanar.accCount_node_pair a l r
  have htl : (Nonplanar.node a {l, r}).leafCountP p = l.leafCountP p + r.leafCountP p := by
    rw [leafCountP_node_of_not p a _ hpa]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
  have hbl := leafCountP_le_accCount p l hl
  have hbr := leafCountP_le_accCount p r hr
  simp only [accCountP, htl, hw]
  omega

end Nonplanar

/-! ### Forest measures -/

namespace Forest

variable {α : Type*}

/-- The number of component trees of a forest (its zeroth Betti number). -/
def b₀ (F : Multiset (Nonplanar α)) : ℕ := Multiset.card F

@[simp] theorem b₀_zero : b₀ (0 : Multiset (Nonplanar α)) = 0 := Multiset.card_zero
@[simp] theorem b₀_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    b₀ (T ::ₘ F) = b₀ F + 1 := Multiset.card_cons T F
@[simp] theorem b₀_singleton (T : Nonplanar α) :
    b₀ ({T} : Multiset (Nonplanar α)) = 1 := Multiset.card_singleton T
@[simp] theorem b₀_add (F G : Multiset (Nonplanar α)) :
    b₀ (F + G) = b₀ F + b₀ G := Multiset.card_add F G

/-- The total non-root vertex count of a forest. -/
def alpha (F : Multiset (Nonplanar α)) : ℕ := (F.map Nonplanar.accCount).sum

@[simp] theorem alpha_zero : alpha (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem alpha_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    alpha (T ::ₘ F) = T.accCount + alpha F := by
  simp only [alpha, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem alpha_singleton (T : Nonplanar α) :
    alpha ({T} : Multiset (Nonplanar α)) = T.accCount := by
  simp only [alpha, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem alpha_add (F G : Multiset (Nonplanar α)) :
    alpha (F + G) = alpha F + alpha G := by
  simp only [alpha, Multiset.map_add, Multiset.sum_add]

/-- `b₀ + alpha`: the total vertex count of a forest (`sigma_eq_sum_numNodes`). -/
def sigma (F : Multiset (Nonplanar α)) : ℕ := b₀ F + alpha F

@[simp] theorem sigma_zero : sigma (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem sigma_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    sigma (T ::ₘ F) = T.numNodes + sigma F := by
  simp only [sigma, b₀_cons, alpha_cons, ← Nonplanar.accCount_add_one]
  omega
@[simp] theorem sigma_singleton (T : Nonplanar α) :
    sigma ({T} : Multiset (Nonplanar α)) = T.numNodes := by
  simp only [sigma, b₀_singleton, alpha_singleton, ← Nonplanar.accCount_add_one]
  omega
@[simp] theorem sigma_add (F G : Multiset (Nonplanar α)) :
    sigma (F + G) = sigma F + sigma G := by
  simp only [sigma, b₀_add, alpha_add]; omega

/-- `sigma` is the total vertex count: the forest case of `#V = b₀ + #E`. -/
theorem sigma_eq_sum_numNodes (F : Multiset (Nonplanar α)) :
    sigma F = (F.map Nonplanar.numNodes).sum := by
  induction F using Multiset.induction with
  | empty => rfl
  | cons T F ih => rw [sigma_cons, ih, Multiset.map_cons, Multiset.sum_cons]


/-- Discounted accessible terms across a forest. -/
def alphaP (p : α → Prop) [DecidablePred p] (F : Multiset (Nonplanar α)) : ℕ :=
  (F.map (Nonplanar.accCountP p)).sum

@[simp] theorem alphaP_zero (p : α → Prop) [DecidablePred p] :
    alphaP p (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem alphaP_cons (p : α → Prop) [DecidablePred p] (T : Nonplanar α)
    (F : Multiset (Nonplanar α)) : alphaP p (T ::ₘ F) = T.accCountP p + alphaP p F := by
  simp only [alphaP, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem alphaP_singleton (p : α → Prop) [DecidablePred p] (T : Nonplanar α) :
    alphaP p ({T} : Multiset (Nonplanar α)) = T.accCountP p := by
  simp only [alphaP, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem alphaP_add (p : α → Prop) [DecidablePred p]
    (F G : Multiset (Nonplanar α)) : alphaP p (F + G) = alphaP p F + alphaP p G := by
  simp only [alphaP, Multiset.map_add, Multiset.sum_add]

/-- Discounted forest size: components plus discounted accessible terms. Unlike
    `sigma`, this is not the vertex count when counted leaves exist. -/
def sigmaP (p : α → Prop) [DecidablePred p] (F : Multiset (Nonplanar α)) : ℕ :=
  b₀ F + alphaP p F

@[simp] theorem sigmaP_zero (p : α → Prop) [DecidablePred p] :
    sigmaP p (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem sigmaP_cons (p : α → Prop) [DecidablePred p] (T : Nonplanar α)
    (F : Multiset (Nonplanar α)) : sigmaP p (T ::ₘ F) = T.accCountP p + 1 + sigmaP p F := by
  simp only [sigmaP, b₀_cons, alphaP_cons]; omega
@[simp] theorem sigmaP_singleton (p : α → Prop) [DecidablePred p] (T : Nonplanar α) :
    sigmaP p ({T} : Multiset (Nonplanar α)) = T.accCountP p + 1 := by
  simp only [sigmaP, b₀_singleton, alphaP_singleton]; omega
@[simp] theorem sigmaP_add (p : α → Prop) [DecidablePred p]
    (F G : Multiset (Nonplanar α)) : sigmaP p (F + G) = sigmaP p F + sigmaP p G := by
  simp only [sigmaP, b₀_add, alphaP_add]; omega

end Forest

end RootedTree
