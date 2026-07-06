/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Counting

/-!
# Trace vocabulary for the leaf statistics
[marcolli-chomsky-berwick-2025]

One-line specializations of the generic leaf statistics and discounted measures
(`leafCountP`, `leafDepthSumP`, `accCountP`, `alphaP`, `sigmaP`) at the trace-marker
color class `Sum.isRight`, under MCB's names (`traceLeafCount`, `traceDepthSum`,
`accCountC`, `alphaC`, `sigmaC`). No independent content.

This file is domain vocabulary and moves out of `Core/` together with the MCB layer of
`Coproduct/Conservation.lean`, which consumes it from the algebra layer.
-/

namespace RoseTree

variable {α β : Type*}

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

theorem traceLeafCount_node_of_ne_nil (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β)))
    (h : cs ≠ []) : traceLeafCount (.node v cs) = (cs.map traceLeafCount).sum :=
  leafCountP_node_of_ne_nil _ v cs h

@[simp] theorem traceLeafCount_node_cons (v : α ⊕ β) (c : RoseTree (α ⊕ β))
    (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node v (c :: cs)) = ((c :: cs).map traceLeafCount).sum :=
  leafCountP_node_cons _ v c cs

@[simp] theorem traceLeafCount_node_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node (Sum.inl a) cs) = (cs.map traceLeafCount).sum :=
  leafCountP_node_of_not _ _ cs (by simp)

@[simp] theorem traceDepthSum_leaf_inl (a : α) :
    traceDepthSum (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 :=
  leafDepthSumP_leaf _ _

@[simp] theorem traceDepthSum_leaf_inr (b : β) :
    traceDepthSum (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 0 :=
  leafDepthSumP_leaf _ _

@[simp] theorem traceDepthSum_node (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    traceDepthSum (.node v cs)
      = (cs.map fun c => traceDepthSum c + traceLeafCount c).sum :=
  leafDepthSumP_node _ v cs

theorem traceLeafCount_perm {t s : RoseTree (α ⊕ β)} (h : Perm t s) :
    t.traceLeafCount = s.traceLeafCount :=
  leafCountP_perm _ h

theorem traceDepthSum_perm {t s : RoseTree (α ⊕ β)} (h : Perm t s) :
    t.traceDepthSum = s.traceDepthSum :=
  leafDepthSumP_perm _ h

theorem traceLeafCount_le_node (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    (cs.map traceLeafCount).sum ≤ traceLeafCount (.node v cs) :=
  sum_map_leafCountP_le_node _ v cs

theorem traceLeafCount_le_numNodes (t : RoseTree (α ⊕ β)) :
    t.traceLeafCount ≤ t.numNodes :=
  leafCountP_le_numNodes _ t

theorem traceLeafCount_lt_numNodes_of_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (RoseTree.node (Sum.inl a) cs) <
      numNodes (RoseTree.node (Sum.inl a) cs) :=
  leafCountP_lt_numNodes_of_not _ _ cs (by simp)

theorem traceLeafCount_le_traceDepthSum_of_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node (Sum.inl a) cs) ≤ traceDepthSum (.node (Sum.inl a) cs) :=
  leafCountP_le_leafDepthSumP_of_not _ _ cs (by simp)

end RoseTree

namespace RootedTree

namespace Nonplanar

variable {α β : Type*}

/-- The number of `Sum.inr`-labeled (trace-marker) leaves of a nonplanar tree. -/
def traceLeafCount : Nonplanar (α ⊕ β) → ℕ := leafCountP (·.isRight = true)

@[simp] theorem traceLeafCount_mk (t : RoseTree (α ⊕ β)) :
    (mk t).traceLeafCount = t.traceLeafCount := rfl

@[simp] theorem traceLeafCount_leaf_inl (a : α) :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).traceLeafCount = 0 := by
  simp [traceLeafCount]

@[simp] theorem traceLeafCount_leaf_inr (b : β) :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).traceLeafCount = 1 := by
  simp [traceLeafCount]

@[simp] theorem traceLeafCount_node_inl (a : α) (F : Multiset (Nonplanar (α ⊕ β))) :
    (Nonplanar.node (Sum.inl a) F).traceLeafCount
      = (F.map Nonplanar.traceLeafCount).sum :=
  leafCountP_node_of_not _ _ F (by simp)

/-- The depth-weighted trace-marker count of a nonplanar tree. -/
def traceDepthSum : Nonplanar (α ⊕ β) → ℕ := leafDepthSumP (·.isRight = true)

@[simp] theorem traceDepthSum_mk (t : RoseTree (α ⊕ β)) :
    (mk t).traceDepthSum = t.traceDepthSum := rfl

@[simp] theorem traceDepthSum_leaf_inl (a : α) :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).traceDepthSum = 0 := by
  simp [traceDepthSum]

@[simp] theorem traceDepthSum_leaf_inr (b : β) :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).traceDepthSum = 0 := by
  simp [traceDepthSum]

@[simp] theorem traceDepthSum_node_inl (a : α) (F : Multiset (Nonplanar (α ⊕ β))) :
    (Nonplanar.node (Sum.inl a) F).traceDepthSum
      = (F.map (fun c => c.traceDepthSum + c.traceLeafCount)).sum :=
  leafDepthSumP_node _ _ F

theorem traceLeafCount_lt_numNodes_of_rootInl (t : Nonplanar (α ⊕ β)) (x : α)
    (h : t.rootValue = Sum.inl x) : t.traceLeafCount < t.numNodes :=
  leafCountP_lt_numNodes_of_not_root _ t (by rw [h]; simp)

theorem traceLeafCount_le_traceDepthSum_of_rootInl (t : Nonplanar (α ⊕ β)) (x : α)
    (h : t.rootValue = Sum.inl x) : t.traceLeafCount ≤ t.traceDepthSum :=
  leafCountP_le_leafDepthSumP_of_not_root _ t (by rw [h]; simp)

/-- The trace-excluding accessible-term count `αᶜ(T) = α(T) − #traceLeaves(T)`. -/
def accCountC : Nonplanar (α ⊕ β) → ℕ := accCountP (·.isRight = true)

@[simp] theorem accCountC_leaf_inl (a : α) :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).accCountC = 0 := rfl

@[simp] theorem accCountC_leaf_inr (b : β) :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).accCountC = 0 := rfl

theorem accCountC_eq (t : Nonplanar (α ⊕ β)) :
    t.accCountC = t.accCount - t.traceLeafCount := rfl

theorem traceLeafCount_le_accCount (t : Nonplanar (α ⊕ β))
    (h : t.traceLeafCount < t.numNodes) : t.traceLeafCount ≤ t.accCount :=
  leafCountP_le_accCount _ t h

/-- External Merge adds two accessible terms in the trace-aware count
    (MCB Lemma 1.6.3, eq. 1.6.5). -/
theorem accCountC_merge (a : α) (l r : Nonplanar (α ⊕ β))
    (hl : l.traceLeafCount < l.numNodes) (hr : r.traceLeafCount < r.numNodes) :
    (Nonplanar.node (Sum.inl a) {l, r}).accCountC = l.accCountC + r.accCountC + 2 :=
  accCountP_node_pair _ _ l r (by simp) hl hr

end Nonplanar

namespace Forest

variable {α β : Type*}

/-- Trace-excluding accessible terms across a workspace, `αᶜ(F) = Σ αᶜ(Tᵢ)`. -/
def alphaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ := alphaP (·.isRight = true) F

theorem alphaC_eq (F : Multiset (Nonplanar (α ⊕ β))) :
    alphaC F = (F.map Nonplanar.accCountC).sum := rfl

@[simp] theorem alphaC_zero : alphaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem alphaC_cons (T : Nonplanar (α ⊕ β)) (F : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (T ::ₘ F) = T.accCountC + alphaC F :=
  alphaP_cons _ T F
@[simp] theorem alphaC_singleton (T : Nonplanar (α ⊕ β)) :
    alphaC ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accCountC :=
  alphaP_singleton _ T
@[simp] theorem alphaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (F + G) = alphaC F + alphaC G :=
  alphaP_add _ F G

/-- Trace-aware workspace size `σᶜ(F) = b₀(F) + αᶜ(F)`; not the vertex count for
    contraction quotients (`σᶜ ≠ #V`, MCB p. 66). -/
def sigmaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ := sigmaP (·.isRight = true) F

theorem sigmaC_eq (F : Multiset (Nonplanar (α ⊕ β))) : sigmaC F = b₀ F + alphaC F := rfl

@[simp] theorem sigmaC_zero : sigmaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem sigmaC_cons (T : Nonplanar (α ⊕ β)) (F : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (T ::ₘ F) = T.accCountC + 1 + sigmaC F :=
  sigmaP_cons _ T F
@[simp] theorem sigmaC_singleton (T : Nonplanar (α ⊕ β)) :
    sigmaC ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accCountC + 1 :=
  sigmaP_singleton _ T
@[simp] theorem sigmaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (F + G) = sigmaC F + sigmaC G :=
  sigmaP_add _ F G

end Forest

end RootedTree
