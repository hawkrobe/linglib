/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Linglib.Core.Data.RoseTree.DecEq
import Linglib.Syntax.Minimalist.Defs

/-!
# Syntactic objects

A syntactic object is a binary rooted tree with leaves labelled by the lexical alphabet and no
labels at internal vertices: an element of the free non-associative commutative magma on `SO₀`.
This file builds two carriers for it over one alphabet `Vertex := LIToken ⊕ Option LIToken`, in
which `Sum.inl tok` is a lexical item, `Sum.inr none` the bare marker, an internal node when
binary and the index-free trace when childless, and `Sum.inr (some tok)` on a leaf the trace of
`tok`, the cancellation `T/T_v` remembering the head of `T_v`. `SyntacticObject` is the
well-formed unordered tree over `Vertex`, the object Merge builds, and `PlanarSyntacticObject` the
well-formed ordered tree, [marcolli-chomsky-berwick-2025]'s planar embedding, the form
linearization and PF read. Well-formedness is stated once, on ordered trees, and descends to the
quotient; `PlanarSyntacticObject.toSyntacticObject` forgets the order and is a homomorphism for
the vocabulary the two carriers share, `leaf`, `trace`, `traceOf` and `merge`.

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

namespace Minimalist

open RoseTree RoseTree.Nonplanar

/-- A vertex: a lexical token on a leaf, the bare marker `Sum.inr none` on an index-free trace
    leaf or an internal node, the two told apart by arity, or the trace of a token. -/
abbrev SyntacticObject.Vertex : Type := LIToken ⊕ Option LIToken

namespace SyntacticObject

/-! ### Well-formedness -/

mutual
/-- Well-formedness of an ordered tree: a lexical or trace vertex is a leaf, and a bare vertex is
    childless or binary with well-formed children. -/
def wellFormed : RoseTree Vertex → Bool
  | .node (.inl _) cs => cs.isEmpty
  | .node (.inr (some _)) cs => cs.isEmpty
  | .node (.inr none) cs => (cs.length == 0 || cs.length == 2) && wellFormedList cs
/-- Every tree in the list is well-formed. -/
def wellFormedList : List (RoseTree Vertex) → Bool
  | [] => true
  | c :: cs => wellFormed c && wellFormedList cs
end

private theorem wellFormed_node_congr {a : Vertex} {cs ds : List (RoseTree Vertex)}
    (hlen : cs.length = ds.length) (hlist : wellFormedList cs = wellFormedList ds) :
    wellFormed (.node a cs) = wellFormed (.node a ds) := by
  match a with
  | .inr none => simp only [wellFormed, hlen, hlist]
  | .inl _ | .inr (some _) =>
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
    wellFormed (.node (Sum.inr none) [l, r]) = (wellFormed l && wellFormed r) := by
  simp [wellFormed, wellFormedList]

/-- Under well-formedness, a node has either no children or exactly two. -/
theorem wellFormed_length {a : Vertex} {cs : List (RoseTree Vertex)}
    (ht : wellFormed (.node a cs) = true) : cs.length = 0 ∨ cs.length = 2 := by
  match a with
  | .inl _ | .inr (some _) =>
    rw [wellFormed, List.isEmpty_iff] at ht
    exact Or.inl (by rw [ht]; rfl)
  | .inr none =>
    rw [wellFormed, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at ht
    exact ht.1

end SyntacticObject

/-- An unordered tree over `Vertex` is a syntactic object when its ordered representatives are
    well-formed: binary, with lexical or trace leaves and bare internal vertices. -/
def IsSyntacticObject (t : Nonplanar SyntacticObject.Vertex) : Prop :=
  Nonplanar.lift SyntacticObject.wellFormed (fun _ _ h => SyntacticObject.wellFormed_perm h) t
    = true

instance : DecidablePred IsSyntacticObject := fun _ => inferInstanceAs (Decidable (_ = true))

@[simp] theorem isSyntacticObject_mk (t : RoseTree SyntacticObject.Vertex) :
    IsSyntacticObject (Nonplanar.mk t) ↔ SyntacticObject.wellFormed t = true := Iff.rfl

/-- The syntactic objects: the well-formed unordered trees over `Vertex`. -/
def SyntacticObject : Type := { t : Nonplanar SyntacticObject.Vertex // IsSyntacticObject t }

/-- The planar syntactic objects: the well-formed ordered trees over `Vertex`,
    [marcolli-chomsky-berwick-2025] §1.12's planar embeddings. -/
def PlanarSyntacticObject : Type :=
  { t : RoseTree SyntacticObject.Vertex // IsSyntacticObject (Nonplanar.mk t) }

instance : DecidableEq SyntacticObject := Subtype.instDecidableEq

instance : DecidableEq PlanarSyntacticObject := Subtype.instDecidableEq

/-! ### The shapes -/

namespace SyntacticObject

/-- A lexical leaf. -/
def leaf (tok : LIToken) : SyntacticObject := ⟨Nonplanar.leaf (Sum.inl tok), rfl⟩

/-- The bare trace: a childless bare vertex, the mark an admissible cut leaves in the remaining
    tree ([marcolli-chomsky-berwick-2025], Definition 1.2.6). It carries no index; `traceOf` is
    the indexed trace. -/
def trace : SyntacticObject := ⟨Nonplanar.leaf (Sum.inr none), by decide⟩

/-- The trace of `tok`. -/
def traceOf (tok : LIToken) : SyntacticObject := ⟨Nonplanar.leaf (Sum.inr (some tok)), rfl⟩

/-- A bare binary node is a syntactic object exactly when both daughters are. -/
theorem isSyntacticObject_merge_iff (a b : Nonplanar Vertex) :
    IsSyntacticObject (Nonplanar.node (Sum.inr none) {a, b}) ↔
      IsSyntacticObject a ∧ IsSyntacticObject b := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  show IsSyntacticObject (Nonplanar.node (Sum.inr none) {Nonplanar.mk pa, Nonplanar.mk pb}) ↔
    IsSyntacticObject (Nonplanar.mk pa) ∧ IsSyntacticObject (Nonplanar.mk pb)
  rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar Vertex))
        = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]
  exact (isSyntacticObject_mk _).trans (by rw [wellFormed_merge, Bool.and_eq_true]; exact Iff.rfl)

/-- Merge on the carrier, the bare binary node over two syntactic objects, also written `*`.
    Noncomputable, since it goes through the smart constructor `Nonplanar.node`; concrete results
    are built ordered and forgotten by `PlanarSyntacticObject.toSyntacticObject`. -/
noncomputable def merge (l r : SyntacticObject) : SyntacticObject :=
  ⟨Nonplanar.node (Sum.inr none) {l.val, r.val}, (isSyntacticObject_merge_iff _ _).2 ⟨l.2, r.2⟩⟩

@[simp] theorem merge_val (l r : SyntacticObject) :
    (merge l r).val = Nonplanar.node (Sum.inr none) {l.val, r.val} := rfl

theorem merge_comm (l r : SyntacticObject) : merge l r = merge r l :=
  Subtype.ext (by rw [merge_val, merge_val, Multiset.pair_comm])

/-- Merge of two ordered-built objects is the ordered binary node, so concrete results reduce. -/
theorem merge_mk (pl pr : RoseTree Vertex)
    (hl : IsSyntacticObject (Nonplanar.mk pl)) (hr : IsSyntacticObject (Nonplanar.mk pr)) :
    (merge ⟨Nonplanar.mk pl, hl⟩ ⟨Nonplanar.mk pr, hr⟩).val
      = Nonplanar.mk (.node (Sum.inr none) [pl, pr]) := by
  rw [merge_val,
      show ({Nonplanar.mk pl, Nonplanar.mk pr} : Multiset (Nonplanar Vertex))
        = Multiset.ofList ([pl, pr].map Nonplanar.mk) from rfl,
      Nonplanar.node_mk_tree_list]

end SyntacticObject

namespace PlanarSyntacticObject

open SyntacticObject (Vertex wellFormed wellFormed_merge)

/-- A lexical leaf. -/
def leaf (tok : LIToken) : PlanarSyntacticObject := ⟨.node (Sum.inl tok) [], rfl⟩

/-- The bare trace. -/
def trace : PlanarSyntacticObject := ⟨.node (Sum.inr none) [], by decide⟩

/-- The trace of `tok`. -/
def traceOf (tok : LIToken) : PlanarSyntacticObject := ⟨.node (Sum.inr (some tok)) [], rfl⟩

/-- Merge, with the daughters in the given order. -/
def merge (l r : PlanarSyntacticObject) : PlanarSyntacticObject :=
  ⟨.node (Sum.inr none) [l.val, r.val], by
    show wellFormed _ = true
    rw [wellFormed_merge, Bool.and_eq_true]; exact ⟨l.2, r.2⟩⟩

@[simp] theorem leaf_val (tok : LIToken) : (leaf tok).val = .node (Sum.inl tok) [] := rfl
@[simp] theorem trace_val : trace.val = .node (Sum.inr none) [] := rfl
@[simp] theorem traceOf_val (tok : LIToken) : (traceOf tok).val = .node (Sum.inr (some tok)) [] :=
  rfl
@[simp] theorem merge_val (l r : PlanarSyntacticObject) :
    (merge l r).val = .node (Sum.inr none) [l.val, r.val] := rfl

/-- Forgetting the order: the quotient map to the syntactic object. -/
def toSyntacticObject (p : PlanarSyntacticObject) : SyntacticObject := ⟨Nonplanar.mk p.val, p.2⟩

@[simp] theorem toSyntacticObject_val (p : PlanarSyntacticObject) :
    p.toSyntacticObject.val = Nonplanar.mk p.val := rfl

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

/-- Induction on syntactic objects: every syntactic object is a lexical leaf, a trace, or the
    Merge of two syntactic objects. -/
@[elab_as_elim]
theorem ind {motive : SyntacticObject → Prop}
    (leaf : ∀ tok, motive (leaf tok))
    (trace : motive trace)
    (traceOf : ∀ tok, motive (traceOf tok))
    (merge : ∀ l r : SyntacticObject, motive l → motive r → motive (merge l r))
    (s : SyntacticObject) : motive s := by
  suffices H : ∀ n (p : RoseTree Vertex) (hp : IsSyntacticObject (Nonplanar.mk p)),
      p.numNodes = n → motive ⟨Nonplanar.mk p, hp⟩ by
    obtain ⟨t, ht⟩ := s
    refine Quotient.inductionOn (motive := fun t => ∀ (ht : IsSyntacticObject t), motive ⟨t, ht⟩)
      t (fun p ht => H p.numNodes p ht rfl) ht
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rintro ⟨lbl, cs⟩ hp hw
    have hpl : wellFormed (RoseTree.node lbl cs) = true := hp
    cases lbl with
    | inl tok =>
      rw [wellFormed] at hpl
      rcases cs with _ | ⟨c, cs'⟩
      · exact leaf tok
      · simp at hpl
    | inr u =>
      cases u with
      | some tok =>
        rw [wellFormed] at hpl
        rcases cs with _ | ⟨c, cs'⟩
        · exact traceOf tok
        · simp at hpl
      | none =>
      rw [wellFormed, Bool.and_eq_true] at hpl
      obtain ⟨hlen, hlist⟩ := hpl
      rcases cs with _ | ⟨pl, _ | ⟨pr, _ | ⟨x, rest⟩⟩⟩
      · exact trace
      · simp at hlen
      · have hl : wellFormed pl = true := wellFormed_of_mem hlist pl (by simp)
        have hr : wellFormed pr = true := wellFormed_of_mem hlist pr (by simp)
        have hmerge : (⟨Nonplanar.mk (RoseTree.node (Sum.inr none) [pl, pr]), hp⟩ : SyntacticObject)
            = SyntacticObject.merge ⟨Nonplanar.mk pl, hl⟩ ⟨Nonplanar.mk pr, hr⟩ :=
          Subtype.ext (merge_mk pl pr hl hr).symm
        rw [hmerge]
        simp only [RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil] at hw
        exact merge _ _ (IH pl.numNodes (by omega) pl hl rfl) (IH pr.numNodes (by omega) pr hr rfl)
      · simp at hlen

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
