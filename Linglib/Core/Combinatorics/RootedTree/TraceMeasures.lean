/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Counting

/-!
# Trace-aware size measures on the contraction-quotient carrier
[marcolli-chomsky-berwick-2025]

The MCB size measures on `Nonplanar (α ⊕ β)`, where `Sum.inl` vertices carry lexical
decorations and `Sum.inr` vertices are trace-marker placeholders left by the Δ^c
coproduct. A trace leaf is a vertex but **not** an accessible term, so the trace-aware
counts subtract the marked-leaf count off the generic measures — and the trace-free
identity `σ = #V` fails on contraction quotients (`σᶜ ≠ #V`, MCB p. 66), witnessed
concretely at the end of the file.

## Main definitions

* `RoseTree.traceLeafCount` / `RoseTree.traceDepthSum` (with `Nonplanar` descents): the
  marker statistics, `leafCountP`/`leafDepthSumP` at the `Sum.isRight` color class.
* `Nonplanar.accCountC`: trace-excluding accessible-term count `α − #traceLeaves`.
* `Forest.alphaC` / `Forest.sigmaC`: the trace-aware workspace measures.

## Main results

* `Nonplanar.accCountC_merge`: External Merge adds two accessible terms in the
  trace-aware count (MCB Lemma 1.6.3, eq. 1.6.5).
-/

namespace RoseTree

variable {α β : Type*}

/-! ### Trace statistics: `leafCountP`/`leafDepthSumP` at the marker color class -/

/-- The number of `Sum.inr`-labeled (trace-marker) leaves in a tree. -/
def traceLeafCount (t : RoseTree (α ⊕ β)) : ℕ := leafCountP (·.isRight = true) t

/-- Sum of root-distances of the `Sum.inr`-labeled (trace-marker) leaves. -/
def traceDepthSum (t : RoseTree (α ⊕ β)) : ℕ := leafDepthSumP (·.isRight = true) t

@[simp] theorem traceLeafCount_leaf_inr (b : β) :
    traceLeafCount (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 1 := by
  simp [traceLeafCount]

@[simp] theorem traceLeafCount_leaf_inl (a : α) :
    traceLeafCount (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 := by
  simp [traceLeafCount]

/-- On a non-leaf node, `traceLeafCount` is the sum of the children's counts,
    regardless of the root label's `Sum`-side. -/
theorem traceLeafCount_node_of_ne_nil (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β)))
    (h : cs ≠ []) : traceLeafCount (.node v cs) = (cs.map traceLeafCount).sum :=
  leafCountP_node_of_ne_nil _ v cs h

@[simp] theorem traceLeafCount_node_cons (v : α ⊕ β) (c : RoseTree (α ⊕ β))
    (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node v (c :: cs)) = ((c :: cs).map traceLeafCount).sum :=
  leafCountP_node_cons _ v c cs

/-- On a `Sum.inl` root the count is just the children's total (the root is never
    itself a trace leaf), for any child list. -/
@[simp] theorem traceLeafCount_node_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node (Sum.inl a) cs) = (cs.map traceLeafCount).sum :=
  leafCountP_node_of_not _ _ cs (by simp)

@[simp] theorem traceDepthSum_leaf_inl (a : α) :
    traceDepthSum (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 :=
  leafDepthSumP_leaf _ _

@[simp] theorem traceDepthSum_leaf_inr (b : β) :
    traceDepthSum (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 0 :=
  leafDepthSumP_leaf _ _

/-- Each child contributes its own trace-depth plus one per trace leaf it carries. -/
@[simp] theorem traceDepthSum_node (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    traceDepthSum (.node v cs)
      = (cs.map fun c => traceDepthSum c + traceLeafCount c).sum :=
  leafDepthSumP_node _ v cs

/-- `traceLeafCount` is a `Perm`-invariant. -/
theorem traceLeafCount_perm {t s : RoseTree (α ⊕ β)} (h : Perm t s) :
    t.traceLeafCount = s.traceLeafCount :=
  leafCountP_perm _ h

/-- `traceDepthSum` is a `Perm`-invariant. -/
theorem traceDepthSum_perm {t s : RoseTree (α ⊕ β)} (h : Perm t s) :
    t.traceDepthSum = s.traceDepthSum :=
  leafDepthSumP_perm _ h

/-- The children's trace leaves are bounded by the node's. -/
theorem traceLeafCount_le_node (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    (cs.map traceLeafCount).sum ≤ traceLeafCount (.node v cs) :=
  sum_map_leafCountP_le_node _ v cs

/-- A trace leaf is a vertex. -/
theorem traceLeafCount_le_numNodes (t : RoseTree (α ⊕ β)) :
    t.traceLeafCount ≤ t.numNodes :=
  leafCountP_le_numNodes _ t

/-- A `Sum.inl`-rooted tree has a non-trace vertex (its root), so its trace leaves
    number strictly fewer than its vertices. -/
theorem traceLeafCount_lt_numNodes_of_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (RoseTree.node (Sum.inl a) cs) <
      numNodes (RoseTree.node (Sum.inl a) cs) :=
  leafCountP_lt_numNodes_of_not _ _ cs (by simp)

/-- A `Sum.inl` root puts every trace leaf at depth ≥ 1, so the depth-weighted count
    dominates the plain count. -/
theorem traceLeafCount_le_traceDepthSum_of_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node (Sum.inl a) cs) ≤ traceDepthSum (.node (Sum.inl a) cs) :=
  leafCountP_le_leafDepthSumP_of_not _ _ cs (by simp)

end RoseTree

namespace RootedTree

namespace Nonplanar

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

/-- The **trace-excluding accessible-term count** `αᶜ(T) = α(T) − #traceLeaves(T)`:
    a trace leaf is a vertex but not an accessible term (MCB p. 66). Truncated
    subtraction handles the all-trace edge case. -/
def accCountC (t : Nonplanar (α ⊕ β)) : ℕ := t.accCount - t.traceLeafCount

@[simp] theorem accCountC_leaf_inl :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).accCountC = 0 := rfl

/-- The truncation case: a bare trace leaf has `α = 0` but one marked leaf. -/
@[simp] theorem accCountC_leaf_inr :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).accCountC = 0 := rfl

/-- The marked leaves of a tree are among its non-root vertices whenever the root is
    unmarked. -/
theorem traceLeafCount_le_accCount (t : Nonplanar (α ⊕ β))
    (h : t.traceLeafCount < t.numNodes) : t.traceLeafCount ≤ t.accCount := by
  rw [Nonplanar.accCount_eq_numNodes_sub_one]
  omega

/-- External Merge adds two accessible terms in the trace-aware count: the two
    children's roots become accessible (MCB Lemma 1.6.3, eq. 1.6.5). Needs each child
    to have a lexical vertex (`traceLeafCount < numNodes`), automatic for a real
    syntactic object. -/
theorem accCountC_merge (l r : Nonplanar (α ⊕ β))
    (hl : l.traceLeafCount < l.numNodes) (hr : r.traceLeafCount < r.numNodes) :
    (Nonplanar.node (Sum.inl a) {l, r}).accCountC = l.accCountC + r.accCountC + 2 := by
  have hw := Nonplanar.accCount_node_pair (Sum.inl a) l r
  have htl : (Nonplanar.node (Sum.inl a) {l, r}).traceLeafCount
      = l.traceLeafCount + r.traceLeafCount := by
    rw [traceLeafCount_node_inl]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
  have hbl := l.traceLeafCount_le_accCount hl
  have hbr := r.traceLeafCount_le_accCount hr
  simp only [accCountC, htl, hw]
  omega

end Nonplanar

/-! ### Trace-aware workspace (forest) measures -/

namespace Forest

variable {α β : Type*}

/-- Trace-excluding accessible terms across a workspace, `αᶜ(F) = Σ αᶜ(Tᵢ)`. -/
def alphaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ :=
  (F.map Nonplanar.accCountC).sum

@[simp] theorem alphaC_zero : alphaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem alphaC_cons (T : Nonplanar (α ⊕ β))
    (F : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (T ::ₘ F) = T.accCountC + alphaC F := by
  simp only [alphaC, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem alphaC_singleton (T : Nonplanar (α ⊕ β)) :
    alphaC ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accCountC := by
  simp only [alphaC, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem alphaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (F + G) = alphaC F + alphaC G := by
  simp only [alphaC, Multiset.map_add, Multiset.sum_add]

/-- Trace-aware workspace size `σᶜ(F) = b₀(F) + αᶜ(F)`. Unlike the generic `σ`, this
    is **not** the vertex count for contraction quotients (`σᶜ ≠ #V`, MCB p. 66): a
    trace leaf raises `#V` without raising `σᶜ`. -/
def sigmaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ := b₀ F + alphaC F

@[simp] theorem sigmaC_zero : sigmaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem sigmaC_cons (T : Nonplanar (α ⊕ β))
    (F : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (T ::ₘ F) = T.accCountC + 1 + sigmaC F := by
  simp only [sigmaC, b₀_cons, alphaC_cons]; omega
@[simp] theorem sigmaC_singleton (T : Nonplanar (α ⊕ β)) :
    sigmaC ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accCountC + 1 := by
  simp only [sigmaC, b₀_singleton, alphaC_singleton]; omega
@[simp] theorem sigmaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (F + G) = sigmaC F + sigmaC G := by
  simp only [sigmaC, b₀_add, alphaC_add]; omega

end Forest

/-! ### The `σᶜ ≠ #V` caveat, concretely

A lexical root over a single trace leaf: `#V = 2` (root + trace leaf) but the trace
leaf contributes no accessible term, so `αᶜ = 0` and `σᶜ = 1`. -/

namespace Nonplanar

variable {α β : Type*}

/-- Minimal contraction-quotient witness for the `σᶜ ≠ #V` caveat. -/
private def traceWitness (a : α) (b : β) : Nonplanar (α ⊕ β) :=
  Nonplanar.mk (.node (Sum.inl a) [.node (Sum.inr b) []])

example (a : α) (b : β) : (traceWitness a b).numNodes = 2 := rfl
example (a : α) (b : β) : (traceWitness a b).traceLeafCount = 1 := rfl
example (a : α) (b : β) : (traceWitness a b).accCountC = 0 := rfl

/-- The trace leaf of `traceWitness` sits at depth 1, so `traceDepthSum = 1`. -/
example (a : α) (b : β) : (traceWitness a b).traceDepthSum = 1 := rfl

/-- A trace leaf two levels down contributes depth 2 to `traceDepthSum`. -/
example (a a' : α) (b : β) :
    Nonplanar.traceDepthSum
      (Nonplanar.mk (.node (Sum.inl a) [.node (Sum.inl a') [.node (Sum.inr b) []]])) = 2 := rfl

/-- Two trace leaves at depths 1 and 2 sum to 3 — the multi-extraction additivity
    `d_v = Σ d_{v_i}` of MCB rule 3. -/
example (a a' : α) (b b' : β) :
    Nonplanar.traceDepthSum
      (Nonplanar.mk (.node (Sum.inl a)
        [.node (Sum.inr b) [], .node (Sum.inl a') [.node (Sum.inr b') []]])) = 3 := rfl

/-- `σᶜ` undercounts `#V` on the contraction quotient: the trace leaf is a vertex but
    not an accessible term. -/
example (a : α) (b : β) :
    Forest.sigmaC ({traceWitness a b} : Multiset (Nonplanar (α ⊕ β))) ≠
      (({traceWitness a b} : Multiset (Nonplanar (α ⊕ β))).map
        Nonplanar.numNodes).sum := by
  simp only [Forest.sigmaC, Forest.b₀_singleton, Forest.alphaC_singleton,
    Multiset.map_singleton, Multiset.sum_singleton,
    show (traceWitness a b).accCountC = 0 from rfl,
    show (traceWitness a b).numNodes = 2 from rfl]
  decide

end Nonplanar

end RootedTree
