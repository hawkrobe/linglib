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

A syntactic object is a binary, nonplanar, rooted tree with leaves labelled by the lexical
alphabet and no labels at internal vertices: the elements of the free non-associative commutative
magma on `SO₀`. This file builds that carrier as the well-formed subset of
`Nonplanar (LIToken ⊕ Option LIToken)`, the same nonplanar trees the Merge algebra is defined
on. The label `Sum.inr none` is the bare marker, its two occurrences told apart by arity: a
childless bare vertex is an index-free trace leaf, a binary bare vertex an internal node. The
label `Sum.inr (some tok)` on a leaf is the trace of `tok`, the cancellation `T/T_v` remembering
the head of `T_v`, which is what chains and their PF reduction read off a single object. The head
of a node is supplied by a head function, not stored on the tree.

## Main definitions

* `Minimalist.SyntacticObject.Vertex`, `Minimalist.IsSyntacticObject`, `Minimalist.SyntacticObject`
* `Minimalist.SyntacticObject.lexLeaf`, `traceLeaf`, `node`: the three shapes.

## Main results

* `Minimalist.SyntacticObject.ind`, `exists_form`: induction and case analysis over the three
  shapes.
* `Minimalist.SyntacticObject.node_mk`: a node of two planar-built objects is the planar node,
  so concrete results are `decide`-able.

## References

* [marcolli-chomsky-berwick-2025], §1.1 (Definition 1.1.1, §1.1.3) and §1.2 (Definitions 1.2.1,
  1.2.6)
-/

namespace Minimalist

open RoseTree RoseTree.Nonplanar

/-- A vertex: a lexical token on a leaf, the bare marker `Sum.inr none` on an index-free trace
    leaf or an internal node, the two told apart by arity, or the trace of a token. -/
abbrev SyntacticObject.Vertex : Type := LIToken ⊕ Option LIToken

/-- The ordered form of a syntactic object: a planar tree of vertices. -/
abbrev Planar : Type := RoseTree SyntacticObject.Vertex

open SyntacticObject

/-- A lexical leaf. -/
abbrev Planar.leaf (tok : LIToken) : Planar := .node (Sum.inl tok) []

/-- The bare trace. -/
abbrev Planar.trace : Planar := .node (Sum.inr none) []

/-- The trace of `tok`. -/
abbrev Planar.traceOf (tok : LIToken) : Planar := .node (Sum.inr (some tok)) []

/-- The Merge of two planar objects. -/
abbrev Planar.merge (l r : Planar) : Planar := .node (Sum.inr none) [l, r]

/-! ### Well-formedness `IsSyntacticObject` (binary, lexical/trace leaves, bare internals) -/

mutual
/-- Well-formedness of a planar tree: a lexical vertex is a leaf, and a bare vertex is either
    childless or binary with well-formed children. -/
def Planar.isSyntacticObject : Planar → Bool
  | .node (.inl _) cs  => cs.isEmpty
  | .node (.inr (some _)) cs => cs.isEmpty
  | .node (.inr none) cs => (cs.length == 0 || cs.length == 2) && Planar.isSyntacticObjectList cs
/-- Every tree in the list is well-formed. -/
def Planar.isSyntacticObjectList : List (Planar) → Bool
  | []      => true
  | c :: cs => Planar.isSyntacticObject c && Planar.isSyntacticObjectList cs
end

/-! ### `Planar.isSyntacticObject` is `Perm`-invariant (so it lifts) -/

/-- Congruence for `Planar.isSyntacticObject` at a node whose children agree in length and in
    `Planar.isSyntacticObjectList`: a lexical label reads only the emptiness (via length), a bare
    label only the arity check (length) and the recursive `Planar.isSyntacticObjectList`. -/
private theorem Planar.isSyntacticObject_node_congr {a : Vertex} {cs ds : List (Planar)}
    (hlen : cs.length = ds.length) (hlist : Planar.isSyntacticObjectList cs
      = Planar.isSyntacticObjectList ds) :
    Planar.isSyntacticObject (.node a cs) = Planar.isSyntacticObject (.node a ds) := by
  match a with
  | .inr none => simp only [Planar.isSyntacticObject, hlen, hlist]
  | .inl _ | .inr (some _) =>
    simp only [Planar.isSyntacticObject]
    rw [Bool.eq_iff_iff]
    simp only [List.isEmpty_iff_length_eq_zero, hlen]

mutual
/-- `Planar.isSyntacticObject` is invariant under `Perm`, hence descends to the quotient. At a node
    the arity check is fixed by the equal children lengths and the recursive check by
    the `PermList` companion. -/
theorem Planar.isSyntacticObject_perm : ∀ {t s : Planar}, RoseTree.Perm t s →
    Planar.isSyntacticObject t = Planar.isSyntacticObject s
  | _, _, .node h => Planar.isSyntacticObject_node_congr h.length_eq
    (Planar.isSyntacticObjectList_permList h)
  | _, _, .trans h₁ h₂ => (Planar.isSyntacticObject_perm h₁).trans
    (Planar.isSyntacticObject_perm h₂)

/-- `Planar.isSyntacticObjectList` is a conjunction over children, hence `PermList`-invariant. -/
theorem Planar.isSyntacticObjectList_permList : ∀ {cs ds : List (Planar)},
    RoseTree.PermList cs ds → Planar.isSyntacticObjectList cs = Planar.isSyntacticObjectList ds
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [Planar.isSyntacticObjectList, Planar.isSyntacticObject_perm h,
      Planar.isSyntacticObjectList_permList hs]
  | _, _, .swap _ _ _ => by simp only [Planar.isSyntacticObjectList, Bool.and_left_comm]
  | _, _, .trans h₁ h₂ => (Planar.isSyntacticObjectList_permList h₁).trans
    (Planar.isSyntacticObjectList_permList h₂)
end

/-! ### The carrier: `IsSyntacticObject` on `Nonplanar` + the `SyntacticObject` subtype -/

/-- Well-formedness on the nonplanar carrier, lifted from `Planar.isSyntacticObject`. -/
def isSyntacticObject : Nonplanar Vertex → Bool :=
  Nonplanar.lift Planar.isSyntacticObject (fun _ _ h => Planar.isSyntacticObject_perm h)

@[simp] theorem isSyntacticObject_mk (t : Planar) : isSyntacticObject (Nonplanar.mk t)
    = Planar.isSyntacticObject t := rfl

/-- A nonplanar tree over `Vertex` is a syntactic object when it is binary with lexical or
    trace leaves and bare internal vertices. -/
def IsSyntacticObject (t : Nonplanar Vertex) : Prop := isSyntacticObject t = true

instance : DecidablePred IsSyntacticObject := fun t => inferInstanceAs (Decidable
    (isSyntacticObject t = true))

/-- The syntactic objects: the well-formed nonplanar trees over `Vertex`. -/
def SyntacticObject : Type := { t : Nonplanar Vertex // IsSyntacticObject t }

instance : DecidableEq SyntacticObject := Subtype.instDecidableEq

/-! ### The three shapes -/

/-- A lexical leaf. -/
def SyntacticObject.lexLeaf (tok : LIToken) : SyntacticObject := ⟨Nonplanar.leaf (Sum.inl tok), rfl⟩

/-- The trace leaf: a childless bare vertex, the mark an admissible cut leaves in the remaining
    tree ([marcolli-chomsky-berwick-2025], Definition 1.2.6). It carries no index; `traceOf` is the
    indexed trace. -/
def SyntacticObject.traceLeaf : SyntacticObject := ⟨Nonplanar.leaf (Sum.inr none), by decide⟩

/-- The trace of `tok`. -/
def SyntacticObject.traceOf (tok : LIToken) : SyntacticObject :=
  ⟨Nonplanar.leaf (Sum.inr (some tok)), rfl⟩

/-- A bare binary node is well-formed exactly when both daughters are. -/
theorem isSyntacticObject_node_pair (a b : Nonplanar Vertex) :
    isSyntacticObject (Nonplanar.node (Sum.inr none) ({a, b} : Multiset (Nonplanar Vertex)))
      = (isSyntacticObject a && isSyntacticObject b) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  show isSyntacticObject (Nonplanar.node (Sum.inr none) {Nonplanar.mk pa, Nonplanar.mk pb})
      = (isSyntacticObject (Nonplanar.mk pa) && isSyntacticObject (Nonplanar.mk pb))
  rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar Vertex))
        = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl,
      Nonplanar.node_mk_tree_list]
  simp only [isSyntacticObject_mk, Planar.isSyntacticObject, Planar.isSyntacticObjectList,
    List.length_cons, List.length_nil,
             Nat.reduceAdd, Nat.reduceBEq, Bool.or_true, Bool.true_and, Bool.and_true]

/-- The bare binary node over two syntactic objects: Merge on the carrier, also written `*`.
    Noncomputable, since it goes through the smart constructor `Nonplanar.node`; concrete
    results are built planar-first and related by `node_mk`. -/
noncomputable def SyntacticObject.node (l r : SyntacticObject) : SyntacticObject :=
  ⟨Nonplanar.node (Sum.inr none) {l.val, r.val}, by
    show isSyntacticObject (Nonplanar.node (Sum.inr none) {l.val, r.val}) = true
    have hl : isSyntacticObject l.val = true := l.2
    have hr : isSyntacticObject r.val = true := r.2
    rw [isSyntacticObject_node_pair, hl, hr, Bool.and_self]⟩

@[simp] theorem SyntacticObject.node_val (l r : SyntacticObject) :
    (SyntacticObject.node l r).val = Nonplanar.node (Sum.inr none) {l.val, r.val} := rfl

/-- A node of two planar-built objects is the planar binary node, so concrete results are
    `decide`-able. -/
theorem SyntacticObject.node_mk (pl pr : Planar)
    (hl : IsSyntacticObject (Nonplanar.mk pl)) (hr : IsSyntacticObject (Nonplanar.mk pr)) :
    (SyntacticObject.node ⟨Nonplanar.mk pl, hl⟩ ⟨Nonplanar.mk pr, hr⟩).val
      = Nonplanar.mk (.node (Sum.inr none) [pl, pr]) := by
  rw [SyntacticObject.node_val,
      show ({Nonplanar.mk pl, Nonplanar.mk pr} : Multiset (Nonplanar Vertex))
        = Multiset.ofList ([pl, pr].map Nonplanar.mk) from rfl,
      Nonplanar.node_mk_tree_list]

/-! ### Induction and case analysis -/

/-- The children of a well-formed node are well-formed. -/
theorem Planar.isSyntacticObject_of_mem {cs : List (Planar)} (h : Planar.isSyntacticObjectList cs
    = true) :
    ∀ c ∈ cs, Planar.isSyntacticObject c = true := by
  induction cs with
  | nil => intro _ hc; exact absurd hc List.not_mem_nil
  | cons hd tl ih =>
    rw [Planar.isSyntacticObjectList, Bool.and_eq_true] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact h.1
    · exact ih h.2 c hmem

/-- Induction on syntactic objects: every syntactic object is a lexical leaf, a trace leaf, or a
    node of two syntactic objects. -/
@[elab_as_elim]
theorem SyntacticObject.ind {motive : SyntacticObject → Prop}
    (lex : ∀ tok, motive (SyntacticObject.lexLeaf tok))
    (trace : motive SyntacticObject.traceLeaf)
    (traceOf : ∀ tok, motive (SyntacticObject.traceOf tok))
    (node : ∀ l r : SyntacticObject, motive l → motive r → motive (SyntacticObject.node l r))
    (s : SyntacticObject) : motive s := by
  suffices H : ∀ n (p : Planar) (hp : IsSyntacticObject (Nonplanar.mk p)),
      p.numNodes = n → motive ⟨Nonplanar.mk p, hp⟩ by
    obtain ⟨t, ht⟩ := s
    refine Quotient.inductionOn (motive := fun t => ∀ (ht : IsSyntacticObject t), motive ⟨t, ht⟩)
      t (fun p ht => H p.numNodes p ht rfl) ht
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rintro ⟨lbl, cs⟩ hp hw
    have hpl : Planar.isSyntacticObject (RoseTree.node lbl cs) = true := hp
    cases lbl with
    | inl tok =>
      rw [Planar.isSyntacticObject] at hpl
      rcases cs with _ | ⟨c, cs'⟩
      · exact lex tok
      · simp at hpl
    | inr u =>
      cases u with
      | some tok =>
        rw [Planar.isSyntacticObject] at hpl
        rcases cs with _ | ⟨c, cs'⟩
        · exact traceOf tok
        · simp at hpl
      | none =>
      rw [Planar.isSyntacticObject, Bool.and_eq_true] at hpl
      obtain ⟨hlen, hlist⟩ := hpl
      rcases cs with _ | ⟨pl, _ | ⟨pr, _ | ⟨x, rest⟩⟩⟩
      · exact trace
      · simp at hlen
      · have hl : Planar.isSyntacticObject pl = true := Planar.isSyntacticObject_of_mem hlist pl
          (by simp)
        have hr : Planar.isSyntacticObject pr = true := Planar.isSyntacticObject_of_mem hlist pr
          (by simp)
        have hnode : (⟨Nonplanar.mk (RoseTree.node (Sum.inr none) [pl, pr]), hp⟩ : SyntacticObject)
            = SyntacticObject.node ⟨Nonplanar.mk pl, hl⟩ ⟨Nonplanar.mk pr, hr⟩ :=
          Subtype.ext (SyntacticObject.node_mk pl pr hl hr).symm
        rw [hnode]
        simp only [RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil] at hw
        exact node _ _ (IH pl.numNodes (by omega) pl hl rfl) (IH pr.numNodes (by omega) pr hr rfl)
      · simp at hlen

/-- Every syntactic object is a lexical leaf, a trace leaf, or a node. -/
theorem SyntacticObject.exists_form (s : SyntacticObject) :
    (∃ tok, s = SyntacticObject.lexLeaf tok) ∨ s = SyntacticObject.traceLeaf ∨
      (∃ tok, s = SyntacticObject.traceOf tok) ∨ (∃ l r, s = SyntacticObject.node l r) := by
  induction s using SyntacticObject.ind with
  | lex tok => exact Or.inl ⟨tok, rfl⟩
  | trace => exact Or.inr (Or.inl rfl)
  | traceOf tok => exact Or.inr (Or.inr (Or.inl ⟨tok, rfl⟩))
  | node l r _ _ => exact Or.inr (Or.inr (Or.inr ⟨l, r, rfl⟩))

end Minimalist
