/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Merge.Internal
public import Linglib.Syntax.Minimalist.Workspace.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Replace
public import Linglib.Syntax.Minimalist.SyntacticObject.Selection
public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Core.Combinatorics.RootedTree.Conservation

/-!
# Merge on the syntactic-object carrier

Merge on the carrier is the bare binary node `SyntacticObject.merge` with root label
`Vertex.bare`. External Merge of two objects is the algebraic Merge operator on the two-object
workspace, at the pruning cuts (`mergeOp_node`) and at the trace cuts (`mergeOpC_node`).

Internal Merge goes through the trace cuts. A moved object leaves the trace of its head
(`headTrace`), so the trace encoder is the head by selection (`traceEncoder`). A uniquely
accessible mover is extracted by exactly one trace cut, whose trunk is the remainder
`deleteAccessible mover current` (`cutSummandsCN_filter_mover`), and Internal Merge is the
composition `M_{T/β,β} ∘ M_{β,1}` of [marcolli-chomsky-berwick-2025] Proposition 1.4.2
(`mergeOpC_im`).

The pruning cuts cannot carry Internal Merge on syntactic objects. A syntactic object is a full
binary tree, so it has an odd number of vertices (`numNodes_odd`); a pruning cut removing one
syntactic object conserves vertices, so it leaves an even number, and the remainder is never a
syntactic object (`not_isSyntacticObject_of_mem_cutSummandsN`): the mover's parent is left unary.

## Main definitions

* `Minimalist.SyntacticObject.traceEncoder`, `headTrace`, `deleteAccessible`

## Main results

* `Minimalist.SyntacticObject.mergeOp_node`, `mergeOpC_node`: External Merge on the carrier.
* `Minimalist.SyntacticObject.cutSummandsCN_filter_mover`: the trace cut extracting a uniquely
  accessible mover leaves `deleteAccessible`.
* `Minimalist.SyntacticObject.mergeOpUnitC_current`, `mergeOpC_im`: Internal Merge on the carrier.
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

/-- External Merge on the carrier is the trace-cut Merge with the bare root label on the
    two-object workspace, for any trace encoder. -/
theorem mergeOpC_node (τ : UnorderedTree Vertex → Option LIToken) (S S' : SyntacticObject) :
    Merge.mergeOpC (R := ℤ) τ Vertex.bare S.val S'.val
        (of' ({S.val, S'.val} : Forest (UnorderedTree Vertex)))
      = of' (R := ℤ) ({(merge S S').val} : Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOpC_pair, merge_val]

/-! ### Internal Merge through the trace cuts -/

/-- The trace encoder of derivations sends a tree to its head by selection. -/
def traceEncoder (t : UnorderedTree Vertex) : Option LIToken := (selCheckN t).head

/-- A moved object leaves the trace of its head by selection, or the bare trace when it has
    none. -/
def headTrace (s : SyntacticObject) : SyntacticObject := s.selHead.elim trace traceOf

/-- The trace a moved object leaves is the trace leaf its encoder labels. -/
theorem headTrace_val (s : SyntacticObject) :
    s.headTrace.val = UnorderedTree.leaf (Sum.inr (traceEncoder s.val)) := by
  show (s.selHead.elim trace traceOf).val = UnorderedTree.leaf (Sum.inr s.selHead)
  cases s.selHead <;> rfl

/-- The remainder `T/mover` is the current object with the mover's occurrences replaced by the
    trace of its head. For a uniquely accessible mover it is the trunk of the trace cut that
    extracts the mover (`cutSummandsCN_filter_mover`); `replace` extends it to a chain of
    occurrences. -/
noncomputable def deleteAccessible (mover current : SyntacticObject) : SyntacticObject :=
  current.replace mover mover.headTrace

@[simp] theorem deleteAccessible_val (mover current : SyntacticObject) :
    (deleteAccessible mover current).val
      = UnorderedTree.replace mover.val mover.headTrace.val current.val := rfl

variable {mover current : SyntacticObject}

/-- A uniquely accessible mover that is not a trace is extracted by exactly one trace cut, whose
    trunk is the remainder `deleteAccessible mover current`. -/
theorem cutSummandsCN_filter_mover (hm : mover.val.value.isLeft)
    (h : current.terms.count mover = 1) (hne : current ≠ mover) :
    (cutSummandsCN traceEncoder current.val).filter (fun p ↦ p.1 = {mover.val})
      = {({mover.val}, (deleteAccessible mover current).val)} := by
  rw [deleteAccessible_val, headTrace_val]
  refine cutSummandsCN_filter_crown_eq_singleton traceEncoder hm ?_
    (fun h' ↦ hne (Subtype.ext h'))
  rw [← map_val_terms, Multiset.count_map_eq_count' _ _ Subtype.val_injective, h]

/-- The unit stage `M_{β,1}` on the current object splits off a uniquely accessible mover beside
    the remainder. -/
theorem mergeOpUnitC_current (hm : mover.val.value.isLeft) (h : current.terms.count mover = 1)
    (hne : current ≠ mover) :
    Merge.mergeOpUnitC (R := ℤ) traceEncoder mover.val
        (of' ({current.val} : Forest (UnorderedTree Vertex)))
      = of' ({mover.val, (deleteAccessible mover current).val} :
          Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOpUnitC, Merge.mergeOpUnitG_apply_singleton_unique _ _ _
      (cutSummandsCN_filter_mover hm h hne) (fun h' ↦ hne (Subtype.ext h')),
    ← of'_singleton, ← of'_add]
  rfl

/-- Internal Merge of a uniquely accessible mover is the composition `M_{T/β,β} ∘ M_{β,1}` of
    trace-cut Merges ([marcolli-chomsky-berwick-2025] Proposition 1.4.2). -/
theorem mergeOpC_im (hm : mover.val.value.isLeft) (h : current.terms.count mover = 1)
    (hne : current ≠ mover) :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare (deleteAccessible mover current).val
        mover.val (Merge.mergeOpUnitC traceEncoder mover.val
          (of' ({current.val} : Forest (UnorderedTree Vertex))))
      = of' (R := ℤ) ({(merge (deleteAccessible mover current) mover).val} :
          Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOpC_im_composition traceEncoder Vertex.bare _ _ _ _
      (cutSummandsCN_filter_mover hm h hne) rfl (fun h' ↦ hne (Subtype.ext h')), merge_val]

private def demoCurrent : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf (mkTraceToken 0))
    (.leaf (mkTraceToken 1))).toSyntacticObject

/-- Raising one daughter of a two-leaf object meets the hypotheses of `mergeOpC_im`. -/
example :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare
        (deleteAccessible (leaf (mkTraceToken 0)) demoCurrent).val (leaf (mkTraceToken 0)).val
        (Merge.mergeOpUnitC traceEncoder (leaf (mkTraceToken 0)).val
          (of' ({demoCurrent.val} : Forest (UnorderedTree Vertex))))
      = of' (R := ℤ) ({(merge (deleteAccessible (leaf (mkTraceToken 0)) demoCurrent)
          (leaf (mkTraceToken 0))).val} : Forest (UnorderedTree Vertex)) :=
  mergeOpC_im (by decide) (by decide) (by decide)

/-! ### The pruning cuts on syntactic objects -/

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
