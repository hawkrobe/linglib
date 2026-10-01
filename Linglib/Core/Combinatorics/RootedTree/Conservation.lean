/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.ContractUnary
public import Linglib.Core.Combinatorics.RootedTree.Cut
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset

@[expose] public section

open RoseTree UnorderedTree

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
* `ConnesKreimer.cutSummandsN_numEdges_single_deletion`: removing one subtree and contracting the
  unary vertex it leaves removes two edges.

## References

* [connes-kreimer-1998]
-/

namespace ConnesKreimer

variable {α : Type*}

/-! ### Vertex conservation for the pruning cuts

The pruning enumeration `cutSummandsP` removes the cut subtrees entirely, leaving nothing in their
place, so vertices are conserved exactly. Contracting the unary vertices of the remainder with
`contractUnary` drops one vertex per contracted vertex. -/

/-- The vertex count contributed by an `Option`-valued deletion remainder. -/
def optNumNodes (o : Option (RoseTree α)) : ℕ := o.elim 0 RoseTree.numNodes

@[simp] private theorem optNumNodes_none : optNumNodes (none : Option (RoseTree α)) = 0 := rfl
@[simp] private theorem optNumNodes_some (t : RoseTree α) : optNumNodes (some t) = t.numNodes := rfl

mutual

/-- Crown vertices plus trunk vertices of a pruning cut recover the tree's vertices exactly. -/
theorem cutSummandsP_numNodes :
    ∀ (t : RoseTree α), ∀ p ∈ cutSummandsP t,
      (Multiset.map RoseTree.numNodes p.1).sum + RoseTree.numNodes p.2 = RoseTree.numNodes t
  | .node a cs => by
    intro p hp
    rw [cutSummandsP_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := cutListSummandsP_numNodes cs q hq
    simp only [RoseTree.numNodes_node]
    omega

/-- Vertex conservation for the deletion cuts of a list of children. -/
theorem cutListSummandsP_numNodes :
    ∀ (cs : List (RoseTree α)), ∀ q ∈ cutListSummandsP cs,
      (Multiset.map RoseTree.numNodes q.1).sum + (q.2.map RoseTree.numNodes).sum
        = (cs.map RoseTree.numNodes).sum
  | [] => by
    intro q hq
    rw [cutListSummandsP_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    rfl
  | t :: ts => by
    intro q hq
    rw [cutListSummandsP_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have h1 := augActionP_numNodes t pr.1 ha
    have h2 := cutListSummandsP_numNodes ts pr.2 hq'
    cases hm : pr.1.2 with
    | none =>
      simp only [hm, optNumNodes_none] at h1
      show (Multiset.map RoseTree.numNodes (pr.1.1 + pr.2.1)).sum
          + (pr.2.2.map RoseTree.numNodes).sum
        = ((t :: ts).map RoseTree.numNodes).sum
      simp only [Multiset.map_add, Multiset.sum_add, List.map_cons, List.sum_cons]
      omega
    | some r =>
      simp only [hm, optNumNodes_some] at h1
      show (Multiset.map RoseTree.numNodes (pr.1.1 + pr.2.1)).sum
          + ((r :: pr.2.2).map RoseTree.numNodes).sum
        = ((t :: ts).map RoseTree.numNodes).sum
      simp only [Multiset.map_add, Multiset.sum_add, List.map_cons, List.sum_cons]
      omega

/-- Vertex conservation for the per-child deletion actions. -/
theorem augActionP_numNodes :
    ∀ (t : RoseTree α), ∀ a ∈ augActionP t,
      (Multiset.map RoseTree.numNodes a.1).sum + optNumNodes a.2 = RoseTree.numNodes t
  | t => by
    intro a ha
    rw [augActionP_eq] at ha
    rcases Multiset.mem_cons.mp ha with h | h
    · obtain rfl := h
      show (Multiset.map RoseTree.numNodes {t}).sum + optNumNodes (none : Option (RoseTree α))
        = RoseTree.numNodes t
      rw [Multiset.map_singleton, Multiset.sum_singleton, optNumNodes_none]
      omega
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      show (Multiset.map RoseTree.numNodes p.1).sum + optNumNodes (some p.2) = RoseTree.numNodes t
      rw [optNumNodes_some]
      exact cutSummandsP_numNodes t p hp

end

/-- Vertex conservation for the nonplanar deletion cuts. -/
theorem cutSummandsN_numNodes (T : UnorderedTree α) :
    ∀ p ∈ cutSummandsN T,
      (p.1.map UnorderedTree.numNodes).sum + p.2.numNodes = T.numNodes := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = UnorderedTree.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsN_mk] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hcons := cutSummandsP_numNodes T₀ q hq
  show ((q.1.map UnorderedTree.mk).map UnorderedTree.numNodes).sum + (UnorderedTree.mk q.2).numNodes
    = (UnorderedTree.mk T₀).numNodes
  rw [UnorderedTree.numNodes_mk, UnorderedTree.numNodes_mk, Multiset.map_map,
      show q.1.map (UnorderedTree.numNodes ∘ UnorderedTree.mk) = q.1.map RoseTree.numNodes from
        Multiset.map_congr rfl (fun x _ => UnorderedTree.numNodes_mk x)]
  exact hcons

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
