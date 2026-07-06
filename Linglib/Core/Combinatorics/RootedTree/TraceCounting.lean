/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Counting

/-!
# Counting marked leaves of a rose tree

For rose trees over `α ⊕ β` whose `Sum.inr`-labeled leaves are *markers*:
`traceLeafCount` counts the marked leaves and `traceDepthSum` weights each by its
root-distance. The two statistics are one paired fold (`traceStats`), so a single
`fold_perm` descends both to the `Nonplanar` quotient.

## Main definitions

* `RoseTree.traceLeafCount`, `RoseTree.traceDepthSum`: the marked-leaf count and its
  depth-weighted refinement, with descents `RootedTree.Nonplanar.traceLeafCount` and
  `RootedTree.Nonplanar.traceDepthSum`.

## Main results

* `RoseTree.traceLeafCount_le_numNodes`: a marked leaf is a vertex; strict for
  `Sum.inl`-rooted trees (`traceLeafCount_lt_numNodes_of_inl`).
* `RoseTree.traceLeafCount_le_traceDepthSum_of_inl`: under a `Sum.inl` root every
  marker sits at depth ≥ 1, so the depth-weighted count dominates the plain one.

`[UPSTREAM]` candidate alongside the `RoseTree` carrier. The `α ⊕ β` labeling is a
2-coloring with decorated colors (Foissy's decorated rooted trees; the bicoloured trees
of partitioned B-series), and the upstream form is the mathlib counting idiom: a leaf
projection (`leafMultiset : Nonplanar α → Multiset α`) with counts as `Multiset.countP`
and the bounds inherited from `countP_le_card` — `trace` is domain vocabulary,
`Sum.isRight` the color-class predicate.
-/

namespace RoseTree

variable {α β : Type*} (a : α) (b : β)

/-! ### Marked-leaf statistics as a paired fold -/

/-- The marked-leaf algebra: `1` at a bare `Sum.inr` leaf, else the children's total. -/
private def tlcAlg (v : α ⊕ β) (ns : List ℕ) : ℕ :=
  match v, ns with
  | Sum.inr _, [] => 1
  | _,         ns => ns.sum

/-- The number of `Sum.inr`-labeled (marked) leaves in a tree. -/
def traceLeafCount : RoseTree (α ⊕ β) → ℕ :=
  fold tlcAlg

/-- The paired statistic `(traceLeafCount t, traceDepthSum t)` as a single fold: the
    depth leg adds, per child, its own depth plus one per marked leaf it carries. -/
private def traceStats : RoseTree (α ⊕ β) → ℕ × ℕ :=
  fold fun v ps => (tlcAlg v (ps.map Prod.fst), (ps.map fun p => p.2 + p.1).sum)

private theorem traceStats_fst (t : RoseTree (α ⊕ β)) :
    (traceStats t).1 = traceLeafCount t :=
  fold_hom Prod.fst (fun _ _ => rfl) t

/-- Sum of root-distances of the `Sum.inr`-labeled (marked) leaves. -/
def traceDepthSum (t : RoseTree (α ⊕ β)) : ℕ := (traceStats t).2

/-! ### Equations -/

@[simp] theorem traceLeafCount_leaf_inr :
    traceLeafCount (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 1 := rfl

@[simp] theorem traceLeafCount_leaf_inl :
    traceLeafCount (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 := rfl

/-- On a non-leaf node, `traceLeafCount` is the sum of the children's counts,
    regardless of the root label's `Sum`-side. Clears the empty/nonempty split. -/
theorem traceLeafCount_node_of_ne_nil (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β)))
    (h : cs ≠ []) : traceLeafCount (.node v cs) = (cs.map traceLeafCount).sum := by
  cases cs with
  | nil => exact absurd rfl h
  | cons c cs => cases v <;> simp only [traceLeafCount, tlcAlg, fold_node, List.map_cons]

@[simp] theorem traceLeafCount_node_cons (v : α ⊕ β) (c : RoseTree (α ⊕ β))
    (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node v (c :: cs)) = ((c :: cs).map traceLeafCount).sum :=
  traceLeafCount_node_of_ne_nil v (c :: cs) (by simp)

/-- On a `Sum.inl` root the count is just the children's total (the root is never
    itself a marked leaf), for any child list. -/
@[simp] theorem traceLeafCount_node_inl (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node (Sum.inl a) cs) = (cs.map traceLeafCount).sum := by
  cases cs with
  | nil => rfl
  | cons c cs => exact traceLeafCount_node_of_ne_nil _ _ (by simp)

@[simp] theorem traceDepthSum_leaf_inl :
    traceDepthSum (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 := rfl

@[simp] theorem traceDepthSum_leaf_inr :
    traceDepthSum (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 0 := rfl

/-- Each child contributes its own depth-weighted count plus one per marked leaf it
    carries (the extra edge from the node to the child). -/
@[simp] theorem traceDepthSum_node (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    traceDepthSum (.node v cs)
      = (cs.map fun c => traceDepthSum c + traceLeafCount c).sum := by
  show (traceStats (.node v cs)).2 = _
  unfold traceStats
  simp only [fold_node, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun c _ =>
    congrArg ((traceStats c).2 + ·) (traceStats_fst c))

/-! ### `Perm` invariance

The paired algebra is permutation-invariant, so one `fold_perm` covers both
statistics. -/

private theorem traceStats_perm {t s : RoseTree (α ⊕ β)} (h : Perm t s) :
    traceStats t = traceStats s := by
  refine fold_perm (fun v l₁ l₂ h' => ?_) h
  refine Prod.ext ?_ ((h'.map _).sum_eq)
  cases l₁ with
  | nil => rw [← h'.nil_eq]
  | cons x xs =>
    cases l₂ with
    | nil => exact absurd h'.eq_nil (by simp)
    | cons y ys => cases v <;> exact (h'.map Prod.fst).sum_eq

/-- `traceLeafCount` is a `Perm`-invariant. -/
theorem traceLeafCount_perm {t s : RoseTree (α ⊕ β)} (h : Perm t s) :
    t.traceLeafCount = s.traceLeafCount := by
  rw [← traceStats_fst, ← traceStats_fst]
  exact congrArg Prod.fst (traceStats_perm h)

/-- `traceDepthSum` is a `Perm`-invariant. -/
theorem traceDepthSum_perm {t s : RoseTree (α ⊕ β)} (h : Perm t s) :
    t.traceDepthSum = s.traceDepthSum :=
  congrArg Prod.snd (traceStats_perm h)

/-! ### Bounds -/

/-- The children's marked leaves are bounded by the node's: a `Sum.inr` root can only
    *add* a marked leaf (the bare-leaf case), never remove one. -/
theorem traceLeafCount_le_node (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    (cs.map traceLeafCount).sum ≤ traceLeafCount (.node v cs) := by
  rcases eq_or_ne cs [] with h | h
  · subst h; exact Nat.zero_le _
  · exact (traceLeafCount_node_of_ne_nil v cs h).ge

mutual
/-- A marked leaf is a vertex, so a tree has at least as many vertices as marked
    leaves. -/
theorem traceLeafCount_le_numNodes :
    ∀ (t : RoseTree (α ⊕ β)), traceLeafCount t ≤ numNodes t
  | .node (Sum.inl _) cs => by
    rw [traceLeafCount_node_inl, numNodes_node]
    have := traceLeafCountSum_le_numNodesSum cs
    omega
  | .node (Sum.inr _) [] => by simp
  | .node (Sum.inr _) (c :: cs) => by
    rw [traceLeafCount_node_cons, numNodes_node]
    have := traceLeafCountSum_le_numNodesSum (c :: cs)
    omega
/-- Auxiliary: the bound summed over a list of children. -/
theorem traceLeafCountSum_le_numNodesSum :
    ∀ (cs : List (RoseTree (α ⊕ β))),
      (cs.map traceLeafCount).sum ≤ (cs.map numNodes).sum
  | [] => by simp
  | c :: cs => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := traceLeafCount_le_numNodes c
    have h2 := traceLeafCountSum_le_numNodesSum cs
    omega
end

/-- A `Sum.inl`-rooted tree has an unmarked vertex (its root), so its marked leaves
    number strictly fewer than its vertices. -/
theorem traceLeafCount_lt_numNodes_of_inl (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (RoseTree.node (Sum.inl a) cs) <
      numNodes (RoseTree.node (Sum.inl a) cs) := by
  rw [traceLeafCount_node_inl, numNodes_node]
  have := traceLeafCountSum_le_numNodesSum cs
  omega

/-- A `Sum.inl` root puts every marked leaf at depth ≥ 1, so the depth-weighted count
    dominates the plain count. -/
theorem traceLeafCount_le_traceDepthSum_of_inl (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node (Sum.inl a) cs) ≤ traceDepthSum (.node (Sum.inl a) cs) := by
  rw [traceLeafCount_node_inl, traceDepthSum_node]
  induction cs with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

end RoseTree

/-! ### Descent to `Nonplanar` -/

namespace RootedTree.Nonplanar

variable {α β : Type*} (a : α) (b : β)

/-- The number of `Sum.inr`-labeled (marked) leaves of a nonplanar tree. -/
def traceLeafCount : Nonplanar (α ⊕ β) → ℕ :=
  Nonplanar.lift RoseTree.traceLeafCount fun _ _ => RoseTree.traceLeafCount_perm

@[simp] theorem traceLeafCount_mk (t : RoseTree (α ⊕ β)) :
    (mk t).traceLeafCount = t.traceLeafCount := rfl

@[simp] theorem traceLeafCount_leaf_inl :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).traceLeafCount = 0 := rfl

@[simp] theorem traceLeafCount_leaf_inr :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).traceLeafCount = 1 := rfl

/-- Marked leaves of a `Sum.inl`-rooted node: the root contributes none, so the count
    is the children's total. -/
@[simp] theorem traceLeafCount_node_inl (F : Multiset (Nonplanar (α ⊕ β))) :
    (Nonplanar.node (Sum.inl a) F).traceLeafCount = (F.map Nonplanar.traceLeafCount).sum := by
  refine Quotient.inductionOn F fun lst => ?_
  show (mk (.node (Sum.inl a) (lst.map Quotient.out))).traceLeafCount = _
  rw [traceLeafCount_mk, RoseTree.traceLeafCount_node_inl, List.map_map]
  simp only [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show (mk (Quotient.out t)).traceLeafCount = Nonplanar.traceLeafCount t
  exact congrArg Nonplanar.traceLeafCount (Quotient.out_eq t)

/-- The depth-weighted marked-leaf count of a nonplanar tree. For a Δ^c cut this reads
    off the total extraction depth of the quotient — see the consumers in
    `Coproduct/Conservation.lean`. -/
def traceDepthSum : Nonplanar (α ⊕ β) → ℕ :=
  Nonplanar.lift RoseTree.traceDepthSum fun _ _ => RoseTree.traceDepthSum_perm

@[simp] theorem traceDepthSum_mk (t : RoseTree (α ⊕ β)) :
    (mk t).traceDepthSum = t.traceDepthSum := rfl

@[simp] theorem traceDepthSum_leaf_inl :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).traceDepthSum = 0 := rfl

@[simp] theorem traceDepthSum_leaf_inr :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).traceDepthSum = 0 := rfl

/-- Each child contributes its own depth-weighted count plus one per marked leaf it
    carries. -/
@[simp] theorem traceDepthSum_node_inl (F : Multiset (Nonplanar (α ⊕ β))) :
    (Nonplanar.node (Sum.inl a) F).traceDepthSum
      = (F.map (fun c => c.traceDepthSum + c.traceLeafCount)).sum := by
  refine Quotient.inductionOn F fun lst => ?_
  show (mk (.node (Sum.inl a) (lst.map Quotient.out))).traceDepthSum = _
  rw [traceDepthSum_mk, RoseTree.traceDepthSum_node, List.map_map]
  simp only [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show RoseTree.traceDepthSum (Quotient.out t) + RoseTree.traceLeafCount (Quotient.out t)
      = Nonplanar.traceDepthSum t + Nonplanar.traceLeafCount t
  congr 1
  · exact congrArg Nonplanar.traceDepthSum (Quotient.out_eq t)
  · exact congrArg Nonplanar.traceLeafCount (Quotient.out_eq t)

/-- A `Sum.inl`-rooted nonplanar tree has an unmarked vertex (its root), so its marked
    leaves number strictly fewer than its vertices. -/
theorem traceLeafCount_lt_numNodes_of_rootInl (t : Nonplanar (α ⊕ β)) (x : α)
    (h : t.rootValue = Sum.inl x) : t.traceLeafCount < t.numNodes := by
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : RoseTree (α ⊕ β), t = Nonplanar.mk t₀ :=
    ⟨t.out, (Quotient.out_eq t).symm⟩
  rw [Nonplanar.rootValue_mk] at h
  cases t₀ with
  | node x cs =>
    rw [RoseTree.value_node] at h
    subst h
    rw [Nonplanar.traceLeafCount_mk, Nonplanar.numNodes_mk]
    exact RoseTree.traceLeafCount_lt_numNodes_of_inl x cs

/-- A `Sum.inl`-rooted nonplanar tree puts every marked leaf at depth ≥ 1, so its
    depth-weighted count dominates its plain count. -/
theorem traceLeafCount_le_traceDepthSum_of_rootInl (t : Nonplanar (α ⊕ β)) (x : α)
    (h : t.rootValue = Sum.inl x) : t.traceLeafCount ≤ t.traceDepthSum := by
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : RoseTree (α ⊕ β), t = Nonplanar.mk t₀ :=
    ⟨t.out, (Quotient.out_eq t).symm⟩
  rw [Nonplanar.rootValue_mk] at h
  cases t₀ with
  | node x cs =>
    rw [RoseTree.value_node] at h
    subst h
    rw [Nonplanar.traceLeafCount_mk, Nonplanar.traceDepthSum_mk]
    exact RoseTree.traceLeafCount_le_traceDepthSum_of_inl x cs

end RootedTree.Nonplanar
