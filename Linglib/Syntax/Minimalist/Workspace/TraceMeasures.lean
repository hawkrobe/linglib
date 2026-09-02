/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Conservation

/-!
# Trace-aware size measures of workspaces

A workspace `F` on the carrier `Nonplanar (α ⊕ β)`, with `Sum.inr` marking a trace, is measured
by its number of components `Multiset.card F`, its number of accessible terms, which are the
non-root vertices `Forest.numEdges F`, and its number of vertices
`Forest.numNodes F = card F + numEdges F`. Under the trace-preserving coproduct a cut leaves a
trace leaf that is not an accessible term, so the trace-aware count discounts trace leaves:
`accessibleCount T = numEdges T − traceLeafCount T` on a tree, summed over a forest, and
`accessibleSize F = card F + accessibleCount F`. The extraction identities say how a Δ^c cut of
a lexical-rooted object splits its accessible terms between crown and trunk, one contraction per
cut.

## Main definitions

* `RoseTree.Nonplanar.accessibleCount`, `Forest.accessibleCount`, `Forest.accessibleSize`

## Main results

* `ConnesKreimer.cutSummandsCN_accessibleCount_single`, `_pair`: the extraction identities.

## References

* [marcolli-chomsky-berwick-2025], §1.6.1–1.6.2 (Lemma 1.6.3)
-/

open RoseTree RoseTree.Nonplanar

namespace RoseTree.Nonplanar

variable {α β : Type*}

/-- `accessibleCount T = numEdges T − traceLeafCount T`, the accessible terms of `T` that are
    not traces. -/
def accessibleCount (t : Nonplanar (α ⊕ β)) : ℕ := t.numEdges - t.traceLeafCount

@[simp] theorem accessibleCount_leaf_inl (a : α) :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).accessibleCount = 0 := rfl

@[simp] theorem accessibleCount_leaf_inr (b : β) :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).accessibleCount = 0 := rfl

private theorem numEdges_sub_leafCountP_node_pair (p : α → Prop) [DecidablePred p] (a : α)
    (l r : Nonplanar α) (hpa : ¬p a)
    (hl : l.leafCountP p < l.numNodes) (hr : r.leafCountP p < r.numNodes) :
    (Nonplanar.node a {l, r}).numEdges - (Nonplanar.node a {l, r}).leafCountP p
      = (l.numEdges - l.leafCountP p) + (r.numEdges - r.leafCountP p) + 2 := by
  have hw := numEdges_node_pair a l r
  have htl : (Nonplanar.node a {l, r}).leafCountP p = l.leafCountP p + r.leafCountP p := by
    rw [leafCountP_node_of_not p a _ hpa]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
  have hbl := leafCountP_le_numEdges p l hl
  have hbr := leafCountP_le_numEdges p r hr
  simp only [htl, hw]
  omega

/-- External Merge adds two accessible terms. -/
theorem accessibleCount_merge (a : α) (l r : Nonplanar (α ⊕ β))
    (hl : l.traceLeafCount < l.numNodes) (hr : r.traceLeafCount < r.numNodes) :
    (Nonplanar.node (Sum.inl a) {l, r}).accessibleCount
      = l.accessibleCount + r.accessibleCount + 2 :=
  numEdges_sub_leafCountP_node_pair _ _ l r (by simp) hl hr

end RoseTree.Nonplanar

namespace Forest

variable {α β : Type*}

/-- The accessible terms of a workspace that are not traces, summed over its components. -/
def accessibleCount (F : Multiset (Nonplanar (α ⊕ β))) : ℕ :=
  (F.map Nonplanar.accessibleCount).sum

@[simp] theorem accessibleCount_zero : accessibleCount (0 : Multiset (Nonplanar (α ⊕ β))) = 0 :=
  rfl
@[simp] theorem accessibleCount_cons (T : Nonplanar (α ⊕ β)) (F : Multiset (Nonplanar (α ⊕ β))) :
    accessibleCount (T ::ₘ F) = T.accessibleCount + accessibleCount F := by
  simp only [accessibleCount, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem accessibleCount_singleton (T : Nonplanar (α ⊕ β)) :
    accessibleCount ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accessibleCount := by
  simp only [accessibleCount, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem accessibleCount_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    accessibleCount (F + G) = accessibleCount F + accessibleCount G := by
  simp only [accessibleCount, Multiset.map_add, Multiset.sum_add]

/-- `accessibleSize F = card F + accessibleCount F`, the trace-aware size of a workspace. -/
def accessibleSize (F : Multiset (Nonplanar (α ⊕ β))) : ℕ :=
  Multiset.card F + accessibleCount F

@[simp] theorem accessibleSize_zero : accessibleSize (0 : Multiset (Nonplanar (α ⊕ β))) = 0 :=
  rfl
@[simp] theorem accessibleSize_cons (T : Nonplanar (α ⊕ β)) (F : Multiset (Nonplanar (α ⊕ β))) :
    accessibleSize (T ::ₘ F) = T.accessibleCount + 1 + accessibleSize F := by
  simp only [accessibleSize, Multiset.card_cons, accessibleCount_cons]; omega
@[simp] theorem accessibleSize_singleton (T : Nonplanar (α ⊕ β)) :
    accessibleSize ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accessibleCount + 1 := by
  simp only [accessibleSize, Multiset.card_singleton, accessibleCount_singleton]; omega
@[simp] theorem accessibleSize_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    accessibleSize (F + G) = accessibleSize F + accessibleSize G := by
  simp only [accessibleSize, Multiset.card_add, accessibleCount_add]; omega

end Forest

namespace ConnesKreimer

variable {α β : Type*}

/-- Contracting one accessible subtree `Tv` out of a lexical-rooted object splits its accessible
    terms as `accessibleCount T = accessibleCount Tv + accessibleCount (T/Tv) + 1`, the `+1`
    being the contraction itself. -/
theorem cutSummandsCN_accessibleCount_single (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) (a₀ : α) (F₀ : Multiset (Nonplanar (α ⊕ β)))
    (hT : T = Nonplanar.node (Sum.inl a₀) F₀)
    (p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
    (Tv : Nonplanar (α ⊕ β)) (hcard : p.1 = {Tv}) :
    T.accessibleCount = Tv.accessibleCount + p.2.accessibleCount + 1 := by
  have hw := cutSummandsCN_numNodes τ T p hp
  have hl := cutSummandsCN_traceLeafCount τ T p hp
  have hTv_lt : Tv.traceLeafCount < Tv.numNodes :=
    cutSummandsCN_crown_traceLeafCount_lt_numNodes τ T p hp Tv
      (by rw [hcard]; exact Multiset.mem_singleton_self Tv)
  have hT_root : T.rootValue = Sum.inl a₀ := by
    rw [hT, Nonplanar.rootValue_node]
  have hT_lt : T.traceLeafCount < T.numNodes :=
    Nonplanar.traceLeafCount_lt_numNodes_of_rootInl T a₀ hT_root
  have hp2_lt : p.2.traceLeafCount < p.2.numNodes :=
    Nonplanar.traceLeafCount_lt_numNodes_of_rootInl p.2 a₀
      ((cutSummandsCN_trunk_rootValue τ T p hp).trans hT_root)
  rw [hcard] at hw hl
  simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_singleton] at hw hl
  simp only [Nonplanar.accessibleCount, Nonplanar.numEdges]
  omega

/-- Contracting two accessible subtrees adds two contractions: `accessibleCount T` is
    `accessibleCount Tv + accessibleCount Tw + accessibleCount (T/{Tv,Tw}) + 2`. -/
theorem cutSummandsCN_accessibleCount_pair (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) (a₀ : α) (F₀ : Multiset (Nonplanar (α ⊕ β)))
    (hT : T = Nonplanar.node (Sum.inl a₀) F₀)
    (p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
    (Tv Tw : Nonplanar (α ⊕ β)) (hcard : p.1 = {Tv, Tw}) :
    T.accessibleCount = Tv.accessibleCount + Tw.accessibleCount + p.2.accessibleCount + 2 := by
  have hw := cutSummandsCN_numNodes τ T p hp
  have hl := cutSummandsCN_traceLeafCount τ T p hp
  have hTv_lt : Tv.traceLeafCount < Tv.numNodes :=
    cutSummandsCN_crown_traceLeafCount_lt_numNodes τ T p hp Tv
      (by rw [hcard]; exact Multiset.mem_cons_self Tv {Tw})
  have hTw_lt : Tw.traceLeafCount < Tw.numNodes :=
    cutSummandsCN_crown_traceLeafCount_lt_numNodes τ T p hp Tw
      (by rw [hcard]; exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self Tw))
  have hT_root : T.rootValue = Sum.inl a₀ := by
    rw [hT, Nonplanar.rootValue_node]
  have hT_lt : T.traceLeafCount < T.numNodes :=
    Nonplanar.traceLeafCount_lt_numNodes_of_rootInl T a₀ hT_root
  have hp2_lt : p.2.traceLeafCount < p.2.numNodes :=
    Nonplanar.traceLeafCount_lt_numNodes_of_rootInl p.2 a₀
      ((cutSummandsCN_trunk_rootValue τ T p hp).trans hT_root)
  rw [hcard] at hw hl
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_cons,
    Multiset.card_singleton] at hw hl
  simp only [Nonplanar.accessibleCount, Nonplanar.numEdges]
  omega

end ConnesKreimer
