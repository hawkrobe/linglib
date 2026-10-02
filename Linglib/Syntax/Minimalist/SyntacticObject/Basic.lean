/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Linglib.Core.Data.UnorderedTree.DecEq
public import Linglib.Syntax.Minimalist.Defs

/-!
# Syntactic objects

A syntactic object is a binary rooted tree with leaves labelled by the lexical alphabet and no
labels at internal vertices: an element of the free non-associative commutative magma on `SO₀`.
This file builds two carriers for it over one alphabet,
`Vertex := Option LIToken ⊕ Option LIToken`. The left summand is structure: a lexical item
`Vertex.lex tok` on a leaf, or the bare label `Vertex.bare` on a binary internal node. The right
summand is a trace: the index-free `Vertex.trace`, or the trace `Vertex.traceOf tok` of a token,
the cancellation `T/T_v` remembering the head of `T_v`. Traces are exactly the right summand, the
convention of the trace coproduct. `SyntacticObject` is the well-formed unordered tree over
`Vertex`, the object Merge builds, and `PlanarSyntacticObject` the well-formed ordered tree,
[marcolli-chomsky-berwick-2025]'s planar embedding, the form linearization and PF read.
Well-formedness is stated once, on ordered trees, and descends to the quotient;
`PlanarSyntacticObject.toSyntacticObject` forgets the order and is a homomorphism for the
vocabulary the two carriers share, `leaf`, `trace`, `traceOf` and `merge`.

## Main definitions

* `Minimalist.SyntacticObject.Vertex`, `Minimalist.IsSyntacticObject`
* `Minimalist.SyntacticObject`, `Minimalist.PlanarSyntacticObject`: the unordered and the ordered
  carrier, each with `leaf`, `trace`, `traceOf` and `merge`.
* `Minimalist.PlanarSyntacticObject.toSyntacticObject`: forgetting the order.

## Main results

* `Minimalist.SyntacticObject.ind`, `exists_form`: induction and case analysis over the shapes.
* `Minimalist.PlanarSyntacticObject.toSyntacticObject_merge`: forgetting the order commutes with
  Merge.

## References

* [marcolli-chomsky-berwick-2025], §1.1 (Definition 1.1.1, §1.1.3), §1.2 (Definitions 1.2.1,
  1.2.6) and §1.12
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree

/-- A vertex carries structure on the left, a lexical token or the bare internal label, and a
    trace on the right, index-free or of a token. -/
abbrev SyntacticObject.Vertex : Type := Option LIToken ⊕ Option LIToken

namespace SyntacticObject

/-- The lexical item `tok` on a leaf. -/
@[match_pattern] abbrev Vertex.lex (tok : LIToken) : Vertex := .inl (some tok)

/-- The bare label of a binary internal node. -/
@[match_pattern] abbrev Vertex.bare : Vertex := .inl none

/-- The index-free trace. -/
@[match_pattern] abbrev Vertex.trace : Vertex := .inr none

/-- The trace of the token `tok`. -/
@[match_pattern] abbrev Vertex.traceOf (tok : LIToken) : Vertex := .inr (some tok)

/-! ### Well-formedness -/

mutual
/-- An ordered tree is well-formed when a lexical or trace vertex is a leaf and a bare vertex is
    binary with well-formed children. -/
def wellFormed : RoseTree Vertex → Bool
  | .node (.inl (some _)) cs => cs.isEmpty
  | .node (.inl none) cs => cs.length == 2 && wellFormedList cs
  | .node (.inr _) cs => cs.isEmpty
/-- Every tree in the list is well-formed. -/
def wellFormedList : List (RoseTree Vertex) → Bool
  | [] => true
  | c :: cs => wellFormed c && wellFormedList cs
end

private theorem wellFormed_node_congr {a : Vertex} {cs ds : List (RoseTree Vertex)}
    (hlen : cs.length = ds.length) (hlist : wellFormedList cs = wellFormedList ds) :
    wellFormed (.node a cs) = wellFormed (.node a ds) := by
  match a with
  | .inl none => simp only [wellFormed, hlen, hlist]
  | .inl (some _) | .inr _ =>
    simp only [wellFormed]
    rw [Bool.eq_iff_iff]
    simp only [List.isEmpty_iff_length_eq_zero, hlen]

mutual
/-- Well-formedness is invariant under permuting children, hence descends to the quotient. -/
theorem wellFormed_perm : ∀ {t s : RoseTree Vertex}, RoseTree.Perm t s →
    wellFormed t = wellFormed s
  | _, _, .node h => wellFormed_node_congr h.length_eq (wellFormedList_permList h)
  | _, _, .trans h₁ h₂ => (wellFormed_perm h₁).trans (wellFormed_perm h₂)

/-- `wellFormedList` is a conjunction over children, hence `PermList`-invariant. -/
theorem wellFormedList_permList : ∀ {cs ds : List (RoseTree Vertex)},
    RoseTree.PermList cs ds → wellFormedList cs = wellFormedList ds
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [wellFormedList, wellFormed_perm h, wellFormedList_permList hs]
  | _, _, .swap _ _ _ => by simp only [wellFormedList, Bool.and_left_comm]
  | _, _, .trans h₁ h₂ => (wellFormedList_permList h₁).trans (wellFormedList_permList h₂)
end

/-- The children of a well-formed list are well-formed. -/
theorem wellFormed_of_mem {cs : List (RoseTree Vertex)} (h : wellFormedList cs = true) :
    ∀ c ∈ cs, wellFormed c = true := by
  induction cs with
  | nil => intro _ hc; exact absurd hc List.not_mem_nil
  | cons hd tl ih =>
    rw [wellFormedList, Bool.and_eq_true] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact h.1
    · exact ih h.2 c hmem

/-- A bare binary node is well-formed exactly when both daughters are. -/
@[simp] theorem wellFormed_merge (l r : RoseTree Vertex) :
    wellFormed (.node Vertex.bare [l, r]) = (wellFormed l && wellFormed r) := by
  simp [wellFormed, wellFormedList]

/-- Under well-formedness, a node has either no children or exactly two. -/
theorem wellFormed_length {a : Vertex} {cs : List (RoseTree Vertex)}
    (ht : wellFormed (.node a cs) = true) : cs.length = 0 ∨ cs.length = 2 := by
  match a with
  | .inl (some _) | .inr _ =>
    rw [wellFormed, List.isEmpty_iff] at ht
    exact Or.inl (by rw [ht]; rfl)
  | .inl none =>
    rw [wellFormed, Bool.and_eq_true, beq_iff_eq] at ht
    exact Or.inr ht.1

end SyntacticObject

/-- An unordered tree over `Vertex` is a syntactic object when its ordered representatives are
    well-formed: binary, with lexical or trace leaves and bare internal vertices. -/
def IsSyntacticObject (t : UnorderedTree SyntacticObject.Vertex) : Prop :=
  Quotient.lift SyntacticObject.wellFormed (fun _ _ h => SyntacticObject.wellFormed_perm h) t
    = true

instance : DecidablePred IsSyntacticObject := fun _ => inferInstanceAs (Decidable (_ = true))

@[simp] theorem isSyntacticObject_mk (t : RoseTree SyntacticObject.Vertex) :
    IsSyntacticObject (UnorderedTree.mk t) ↔ SyntacticObject.wellFormed t = true := Iff.rfl

/-- The syntactic objects are the well-formed unordered trees over `Vertex`. -/
def SyntacticObject : Type := { t : UnorderedTree SyntacticObject.Vertex // IsSyntacticObject t }

/-- The planar syntactic objects are the well-formed ordered trees over `Vertex`,
    [marcolli-chomsky-berwick-2025] §1.12's planar embeddings. -/
def PlanarSyntacticObject : Type :=
  { t : RoseTree SyntacticObject.Vertex // IsSyntacticObject (UnorderedTree.mk t) }

instance : DecidableEq SyntacticObject := Subtype.instDecidableEq

instance : DecidableEq PlanarSyntacticObject := Subtype.instDecidableEq

/-! ### The shapes -/

namespace SyntacticObject

/-- A lexical leaf. -/
@[coe] def leaf (tok : LIToken) : SyntacticObject := ⟨UnorderedTree.leaf (Vertex.lex tok), rfl⟩

/-- The index-free trace, the mark an admissible cut leaves in the remaining tree
    ([marcolli-chomsky-berwick-2025], Definition 1.2.6); `traceOf` is the indexed trace. -/
def trace : SyntacticObject := ⟨UnorderedTree.leaf Vertex.trace, rfl⟩

/-- The trace of `tok`. -/
def traceOf (tok : LIToken) : SyntacticObject := ⟨UnorderedTree.leaf (Vertex.traceOf tok), rfl⟩

@[simp] theorem leaf_val (tok : LIToken) : (leaf tok).val = UnorderedTree.leaf (Vertex.lex tok) :=
  rfl

@[simp] theorem leaf_inj {a b : LIToken} : leaf a = leaf b ↔ a = b :=
  ⟨fun h ↦ Option.some_injective _
    (Sum.inl_injective (congrArg (fun s : SyntacticObject ↦ s.val.value) h)), congrArg leaf⟩
@[simp] theorem trace_val : trace.val = UnorderedTree.leaf Vertex.trace := rfl
@[simp] theorem traceOf_val (tok : LIToken) :
    (traceOf tok).val = UnorderedTree.leaf (Vertex.traceOf tok) := rfl

/-- A bare binary node is a syntactic object exactly when both daughters are. -/
theorem isSyntacticObject_merge_iff (a b : UnorderedTree Vertex) :
    IsSyntacticObject (UnorderedTree.node Vertex.bare {a, b}) ↔
      IsSyntacticObject a ∧ IsSyntacticObject b := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  show IsSyntacticObject (UnorderedTree.node Vertex.bare {UnorderedTree.mk pa,
    UnorderedTree.mk pb}) ↔
    IsSyntacticObject (UnorderedTree.mk pa) ∧ IsSyntacticObject (UnorderedTree.mk pb)
  rw [show ({UnorderedTree.mk pa, UnorderedTree.mk pb} : Multiset (UnorderedTree Vertex))
        = Multiset.ofList ([pa, pb].map UnorderedTree.mk) from rfl, UnorderedTree.node_mk_tree_list]
  exact (isSyntacticObject_mk _).trans (by rw [wellFormed_merge, Bool.and_eq_true]; exact Iff.rfl)

/-- Merge on the carrier, the bare binary node over two syntactic objects, also written `*`.
    Noncomputable, since it goes through the smart constructor `UnorderedTree.node`; concrete
    results are built ordered and forgotten by `PlanarSyntacticObject.toSyntacticObject`. -/
noncomputable def merge (l r : SyntacticObject) : SyntacticObject :=
  ⟨UnorderedTree.node Vertex.bare {l.val, r.val}, (isSyntacticObject_merge_iff _ _).2 ⟨l.2, r.2⟩⟩

@[simp] theorem merge_val (l r : SyntacticObject) :
    (merge l r).val = UnorderedTree.node Vertex.bare {l.val, r.val} := rfl

theorem merge_comm (l r : SyntacticObject) : merge l r = merge r l :=
  Subtype.ext (by rw [merge_val, merge_val, Multiset.pair_comm])

/-- Merge of two ordered-built objects is the ordered binary node, so concrete results reduce. -/
theorem merge_mk (pl pr : RoseTree Vertex)
    (hl : IsSyntacticObject (UnorderedTree.mk pl)) (hr : IsSyntacticObject (UnorderedTree.mk pr)) :
    (merge ⟨UnorderedTree.mk pl, hl⟩ ⟨UnorderedTree.mk pr, hr⟩).val
      = UnorderedTree.mk (.node Vertex.bare [pl, pr]) := by
  rw [merge_val,
      show ({UnorderedTree.mk pl, UnorderedTree.mk pr} : Multiset (UnorderedTree Vertex))
        = Multiset.ofList ([pl, pr].map UnorderedTree.mk) from rfl,
      UnorderedTree.node_mk_tree_list]

end SyntacticObject

namespace PlanarSyntacticObject

open SyntacticObject (Vertex wellFormed wellFormed_merge)

/-- A lexical leaf. -/
@[coe] def leaf (tok : LIToken) : PlanarSyntacticObject := ⟨.node (Vertex.lex tok) [], rfl⟩

/-- The index-free trace. -/
def trace : PlanarSyntacticObject := ⟨.node Vertex.trace [], rfl⟩

/-- The trace of `tok`. -/
def traceOf (tok : LIToken) : PlanarSyntacticObject := ⟨.node (Vertex.traceOf tok) [], rfl⟩

/-- Merge, with the daughters in the given order. -/
def merge (l r : PlanarSyntacticObject) : PlanarSyntacticObject :=
  ⟨.node Vertex.bare [l.val, r.val], by
    show wellFormed _ = true
    rw [wellFormed_merge, Bool.and_eq_true]; exact ⟨l.2, r.2⟩⟩

@[simp] theorem leaf_val (tok : LIToken) : (leaf tok).val = .node (Vertex.lex tok) [] := rfl
@[simp] theorem trace_val : trace.val = .node Vertex.trace [] := rfl
@[simp] theorem traceOf_val (tok : LIToken) : (traceOf tok).val = .node (Vertex.traceOf tok) [] :=
  rfl
@[simp] theorem merge_val (l r : PlanarSyntacticObject) :
    (merge l r).val = .node Vertex.bare [l.val, r.val] := rfl

/-- Forgetting the order is the quotient map to the syntactic object. -/
@[coe] def toSyntacticObject (p : PlanarSyntacticObject)
  : SyntacticObject := ⟨UnorderedTree.mk p.val, p.2⟩

@[simp] theorem toSyntacticObject_val (p : PlanarSyntacticObject) :
    p.toSyntacticObject.val = UnorderedTree.mk p.val := rfl

@[simp] theorem toSyntacticObject_leaf (tok : LIToken) :
    (leaf tok).toSyntacticObject = SyntacticObject.leaf tok := rfl

@[simp] theorem toSyntacticObject_trace : trace.toSyntacticObject = SyntacticObject.trace := rfl

@[simp] theorem toSyntacticObject_traceOf (tok : LIToken) :
    (traceOf tok).toSyntacticObject = SyntacticObject.traceOf tok := rfl

/-- Forgetting the order commutes with Merge. -/
@[simp] theorem toSyntacticObject_merge (l r : PlanarSyntacticObject) :
    (merge l r).toSyntacticObject = SyntacticObject.merge l.toSyntacticObject r.toSyntacticObject :=
  Subtype.ext (SyntacticObject.merge_mk l.val r.val l.2 r.2).symm

end PlanarSyntacticObject

/-! ### Induction and case analysis -/

namespace SyntacticObject

/-- Induction on syntactic objects, each of which is a lexical leaf, a trace, or the Merge of two
    syntactic objects. -/
@[elab_as_elim]
theorem ind {motive : SyntacticObject → Prop}
    (leaf : ∀ tok, motive (leaf tok))
    (trace : motive trace)
    (traceOf : ∀ tok, motive (traceOf tok))
    (merge : ∀ l r : SyntacticObject, motive l → motive r → motive (merge l r))
    (s : SyntacticObject) : motive s := by
  suffices H : ∀ n (p : RoseTree Vertex) (hp : IsSyntacticObject (UnorderedTree.mk p)),
      p.numNodes = n → motive ⟨UnorderedTree.mk p, hp⟩ by
    obtain ⟨t, ht⟩ := s
    refine Quotient.inductionOn (motive := fun t => ∀ (ht : IsSyntacticObject t), motive ⟨t, ht⟩)
      t (fun p ht => H p.numNodes p ht rfl) ht
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rintro ⟨lbl, cs⟩ hp hw
    have hpl : wellFormed (RoseTree.node lbl cs) = true := hp
    cases lbl with
    | inl o =>
      cases o with
      | some tok =>
        rw [wellFormed] at hpl
        rcases cs with _ | ⟨c, cs'⟩
        · exact leaf tok
        · simp at hpl
      | none =>
        rw [wellFormed, Bool.and_eq_true] at hpl
        obtain ⟨hlen, hlist⟩ := hpl
        rcases cs with _ | ⟨pl, _ | ⟨pr, _ | ⟨x, rest⟩⟩⟩
        · simp at hlen
        · simp at hlen
        · have hl : wellFormed pl = true := wellFormed_of_mem hlist pl (by simp)
          have hr : wellFormed pr = true := wellFormed_of_mem hlist pr (by simp)
          have hmerge : (⟨UnorderedTree.mk (RoseTree.node Vertex.bare [pl, pr]), hp⟩
            : SyntacticObject)
              = SyntacticObject.merge ⟨UnorderedTree.mk pl, hl⟩ ⟨UnorderedTree.mk pr, hr⟩ :=
            Subtype.ext (merge_mk pl pr hl hr).symm
          rw [hmerge]
          simp only [RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil] at hw
          exact merge _ _ (IH pl.numNodes (by omega) pl hl rfl)
            (IH pr.numNodes (by omega) pr hr rfl)
        · simp at hlen
    | inr u =>
      rw [wellFormed] at hpl
      rcases cs with _ | ⟨c, cs'⟩
      · cases u with
        | some tok => exact traceOf tok
        | none => exact trace
      · simp at hpl

/-- Every syntactic object is a lexical leaf, a trace, or a Merge. -/
theorem exists_form (s : SyntacticObject) :
    (∃ tok, s = leaf tok) ∨ s = trace ∨ (∃ tok, s = traceOf tok) ∨ (∃ l r, s = merge l r) := by
  induction s using ind with
  | leaf tok => exact Or.inl ⟨tok, rfl⟩
  | trace => exact Or.inr (Or.inl rfl)
  | traceOf tok => exact Or.inr (Or.inr (Or.inl ⟨tok, rfl⟩))
  | merge l r _ _ => exact Or.inr (Or.inr (Or.inr ⟨l, r, rfl⟩))

end SyntacticObject

end Minimalist
