/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Merge.Internal
public import Linglib.Syntax.Minimalist.Workspace.Basic
public import Linglib.Core.Combinatorics.RootedTree.Conservation

/-!
# Merge on the syntactic-object carrier

Merge on the carrier is the bare binary node `SyntacticObject.merge` with root label
`Vertex.bare`. External Merge of two objects is the algebraic Merge operator of
`Merge/Basic.lean` on the two-object workspace (`mergeOp_node`).

Internal Merge cannot be stated through the pruning coproduct on syntactic objects. A syntactic
object is a full binary tree, so it has an odd number of vertices (`numNodes_odd`); a pruning cut
removing one syntactic object conserves vertices, so it leaves an even number, and the remainder
is never a syntactic object (`not_isSyntacticObject_of_mem_cutSummandsN`): the mover's parent is
left unary. Internal Merge on syntactic objects goes through the trace coproduct, whose
remainders keep a trace leaf in the mover's place.

## Main results

* `Minimalist.SyntacticObject.mergeOp_node`: External Merge on the carrier is `mergeOp`.
* `Minimalist.SyntacticObject.numNodes_odd`: a syntactic object has an odd number of vertices.
* `Minimalist.SyntacticObject.not_isSyntacticObject_of_mem_cutSummandsN`: no pruning cut removing
  one syntactic object from another leaves a syntactic object.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.SyntacticObject

open RoseTree UnorderedTree ConnesKreimer

/-- External Merge on the carrier is the algebraic Merge with the bare root label on the
    two-object workspace. -/
theorem mergeOp_node (S S' : SyntacticObject) :
    Merge.mergeOp (R := ℤ) Vertex.bare S.val S'.val
        (of' ({S.val, S'.val} : Forest (UnorderedTree Vertex)))
      = of' (R := ℤ) ({(merge S S').val} : Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOp_pair, merge_val]

mutual
private theorem odd_numNodes_of_wellFormed : ∀ {t : RoseTree Vertex}, wellFormed t = true →
    Odd t.numNodes
  | .node (.inl (some _)) cs, h => by
    rw [wellFormed, List.isEmpty_iff] at h; subst h; simp
  | .node (.inr _) cs, h => by
    rw [wellFormed, List.isEmpty_iff] at h; subst h; simp
  | .node (.inl none) cs, h => by
    rw [wellFormed, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hlen, hl⟩ := h
    match cs, hlen, hl with
    | [a, b], _, hl =>
      simp only [wellFormedList, Bool.and_eq_true] at hl
      obtain ⟨x, hx⟩ := odd_numNodes_of_wellFormed hl.1
      obtain ⟨y, hy⟩ := odd_numNodes_of_wellFormed hl.2.1
      simp only [RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      exact ⟨x + y + 1, by omega⟩
    | [], h, _ => simp at h
    | [_], h, _ => simp at h
    | _ :: _ :: _ :: _, h, _ => simp at h
end

/-- A syntactic object, being a full binary tree, has an odd number of vertices. -/
theorem numNodes_odd (s : SyntacticObject) : Odd s.val.numNodes := by
  obtain ⟨t, ht⟩ := s
  induction t using Quotient.inductionOn with
  | h t => exact odd_numNodes_of_wellFormed ht

/-- A pruning cut removing one syntactic object from another leaves no syntactic object: the
    remainder has an even number of vertices. -/
theorem not_isSyntacticObject_of_mem_cutSummandsN {T mover : SyntacticObject}
    {p : Forest (UnorderedTree Vertex) × UnorderedTree Vertex} (hp : p ∈ cutSummandsN T.val)
    (hcrown : p.1 = {mover.val}) : ¬ IsSyntacticObject p.2 := fun h ↦ by
  have hw := cutSummandsN_numNodes T.val p hp
  rw [hcrown, Multiset.map_singleton, Multiset.sum_singleton] at hw
  obtain ⟨a, ha⟩ := numNodes_odd mover
  obtain ⟨b, hb⟩ := numNodes_odd ⟨p.2, h⟩
  obtain ⟨c, hc⟩ := numNodes_odd T
  simp only at hb
  omega

end Minimalist.SyntacticObject
