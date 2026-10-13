/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.ContractUnary
public import Linglib.Core.Combinatorics.RootedTree.Cut
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Vertex conservation for pruning cuts

A pruning cut removes its crown subtrees entirely, so crown vertices and trunk vertices recover
the vertices of the tree exactly. Hence every crown component, and the trunk of a proper cut, is
smaller than the tree: the descent that makes recursions over cuts, such as the antipode, well
founded.

## Main results

* `ConnesKreimer.cutSummandsN_numNodes`: vertex conservation for the nonplanar pruning cuts.
* `ConnesKreimer.cutSummandsN_crown_numNodes_lt`, `ConnesKreimer.cutSummandsN_trunk_numNodes_lt`:
  crowns and proper trunks are smaller than the tree.
* `ConnesKreimer.cutSummandsN_crown_numEdges_lt`: a nonempty crown has fewer edges than the tree.
* `ConnesKreimer.cutSummandsN_numEdges_single_deletion`: removing one subtree and contracting the
  unary vertex it leaves removes two edges.

## References

* [connes-kreimer-1998]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

variable {α : Type*}

/-! ### Vertex conservation for the pruning cuts -/

/-- The crown and the trunk of a pruning cut have exactly the vertices of the tree. -/
theorem cutSummandsN_numNodes (T : UnorderedTree α) :
    ∀ p ∈ cutSummandsN T,
      (p.1.map UnorderedTree.numNodes).sum + p.2.numNodes = T.numNodes :=
  Quotient.inductionOn T fun t p hp ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsN_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    simpa [projSummand, Multiset.map_map, Function.comp_def] using
      cutSummandsG_numNodes pruning (k := 0) (fun _ _ h ↦ by cases h; rfl) t q hq

/-- No deletion cut extracts the whole tree as its crown; the full-tree extraction is the
    separate primitive term of the coproduct. -/
theorem cutSummandsN_crown_ne_singleton (T : UnorderedTree α)
    (p : Multiset (UnorderedTree α) × UnorderedTree α) (hp : p ∈ cutSummandsN T) :
    p.1 ≠ ({T} : Multiset (UnorderedTree α)) := by
  intro hcrown
  have hw := cutSummandsN_numNodes T p hp
  rw [hcrown] at hw
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at hw
  have := p.2.numNodes_pos
  omega

/-- Every crown component of a deletion cut has fewer vertices than the tree. -/
theorem cutSummandsN_crown_numNodes_lt {T : UnorderedTree α}
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cutSummandsN T)
    {t : UnorderedTree α} (ht : t ∈ p.1) : t.numNodes < T.numNodes := by
  have hw := cutSummandsN_numNodes T p hp
  have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem UnorderedTree.numNodes ht)
  have := p.2.numNodes_pos
  omega

/-- The trunk of a deletion cut with a nonempty crown has fewer vertices than the tree. -/
theorem cutSummandsN_trunk_numNodes_lt {T : UnorderedTree α}
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cutSummandsN T)
    (h : p.1 ≠ 0) : p.2.numNodes < T.numNodes := by
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero h
  have hw := cutSummandsN_numNodes T p hp
  have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem UnorderedTree.numNodes ht)
  have := t.numNodes_pos
  omega

/-- A nonempty crown of a deletion cut has fewer edges in total than the tree. -/
theorem cutSummandsN_crown_numEdges_lt {T : UnorderedTree α}
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cutSummandsN T)
    (h : p.1 ≠ 0) : (p.1.map UnorderedTree.numEdges).sum < T.numEdges := by
  have hw := cutSummandsN_numNodes T p hp
  rw [UnorderedTree.sum_map_numNodes] at hw
  have := Multiset.card_pos.mpr h
  have := p.2.numNodes_pos
  have := T.numEdges_add_one
  omega

/-- No deletion cut of `T` has `T` itself among its crown components. -/
theorem cutSummandsN_self_not_mem_crown (T : UnorderedTree α)
    (p : Multiset (UnorderedTree α) × UnorderedTree α) (hp : p ∈ cutSummandsN T) :
    T ∉ p.1 :=
  fun h ↦ (cutSummandsN_crown_numNodes_lt hp h).false

/-- Deleting one subtree `mover` and contracting the unary vertex it leaves removes two edges,
    the subtree's own edge and the contracted parent.
    `numUnary p.2 = 1` says the cut was a single edge at a
    binary node. -/
theorem cutSummandsN_numEdges_single_deletion (T : UnorderedTree α)
    (p : Multiset (UnorderedTree α) × UnorderedTree α) (hp : p ∈ cutSummandsN T)
    (mover : UnorderedTree α) (hcard : p.1 = {mover}) (huc : p.2.numUnary = 1) :
    T.numEdges = mover.numEdges + (UnorderedTree.contractUnary p.2).numEdges + 2 := by
  have hw := cutSummandsN_numNodes T p hp
  have hcu := UnorderedTree.numNodes_contractUnary_add_numUnary p.2
  have hmT := T.numNodes_pos
  have hmm := mover.numNodes_pos
  have hmp := p.2.numNodes_pos
  have hmc := (UnorderedTree.contractUnary p.2).numNodes_pos
  rw [hcard] at hw
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at hw
  rw [huc] at hcu
  simp only [UnorderedTree.numEdges]
  omega

end ConnesKreimer
