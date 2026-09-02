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
`Nonplanar (LIToken ⊕ Unit)`, the same nonplanar trees the Merge algebra is defined on. The
label `Sum.inr ()` is the single bare marker, and its two occurrences are told apart by arity: a
childless bare vertex is a trace leaf, a binary bare vertex is an internal node. Chain identity
is a property of workspaces, so the trace leaf carries no index, and the head of a node is
supplied by a head function, not stored on the tree.

## Main definitions

* `Minimalist.SOLabel`, `Minimalist.IsSO`, `Minimalist.SyntacticObject`
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

/-- The label alphabet: a lexical token on a leaf, or the bare marker `Sum.inr ()` on a trace
    leaf or an internal node, the two told apart by arity. -/
abbrev SOLabel : Type := LIToken ⊕ Unit

/-! ### Well-formedness `IsSO` (binary, lexical/trace leaves, bare internals) -/

mutual
/-- Well-formedness of a planar tree: a lexical vertex is a leaf, and a bare vertex is either
    childless or binary with well-formed children. -/
def isSOPlanar : RoseTree SOLabel → Bool
  | .node (.inl _) cs  => cs.isEmpty
  | .node (.inr ()) cs => (cs.length == 0 || cs.length == 2) && isSOPlanarList cs
/-- Every tree in the list is well-formed. -/
def isSOPlanarList : List (RoseTree SOLabel) → Bool
  | []      => true
  | c :: cs => isSOPlanar c && isSOPlanarList cs
end

/-! ### `isSOPlanar` is `Perm`-invariant (so it lifts) -/

/-- Congruence for `isSOPlanar` at a node whose children agree in length and in
    `isSOPlanarList`: a lexical label reads only the emptiness (via length), a bare
    label only the arity check (length) and the recursive `isSOPlanarList`. -/
private theorem isSOPlanar_node_congr {a : SOLabel} {cs ds : List (RoseTree SOLabel)}
    (hlen : cs.length = ds.length) (hlist : isSOPlanarList cs = isSOPlanarList ds) :
    isSOPlanar (.node a cs) = isSOPlanar (.node a ds) := by
  cases a with
  | inl _ =>
    simp only [isSOPlanar]
    rw [Bool.eq_iff_iff]
    simp only [List.isEmpty_iff_length_eq_zero, hlen]
  | inr u => cases u; simp only [isSOPlanar, hlen, hlist]

mutual
/-- `isSOPlanar` is invariant under `Perm`, hence descends to the quotient. At a node
    the arity check is fixed by the equal children lengths and the recursive check by
    the `PermList` companion. -/
theorem isSOPlanar_perm : ∀ {t s : RoseTree SOLabel}, RoseTree.Perm t s →
    isSOPlanar t = isSOPlanar s
  | _, _, .node h => isSOPlanar_node_congr h.length_eq (isSOPlanarList_permList h)
  | _, _, .trans h₁ h₂ => (isSOPlanar_perm h₁).trans (isSOPlanar_perm h₂)

/-- `isSOPlanarList` is a conjunction over children, hence `PermList`-invariant. -/
theorem isSOPlanarList_permList : ∀ {cs ds : List (RoseTree SOLabel)},
    RoseTree.PermList cs ds → isSOPlanarList cs = isSOPlanarList ds
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [isSOPlanarList, isSOPlanar_perm h, isSOPlanarList_permList hs]
  | _, _, .swap _ _ _ => by simp only [isSOPlanarList, Bool.and_left_comm]
  | _, _, .trans h₁ h₂ => (isSOPlanarList_permList h₁).trans (isSOPlanarList_permList h₂)
end

/-! ### The carrier: `IsSO` on `Nonplanar` + the `SyntacticObject` subtype -/

/-- Well-formedness on the nonplanar carrier, lifted from `isSOPlanar`. -/
def isSO : Nonplanar SOLabel → Bool :=
  Nonplanar.lift isSOPlanar (fun _ _ h => isSOPlanar_perm h)

@[simp] theorem isSO_mk (t : RoseTree SOLabel) : isSO (Nonplanar.mk t) = isSOPlanar t := rfl

/-- A nonplanar tree over `SOLabel` is a syntactic object when it is binary with lexical or
    trace leaves and bare internal vertices. -/
def IsSO (t : Nonplanar SOLabel) : Prop := isSO t = true

instance : DecidablePred IsSO := fun t => inferInstanceAs (Decidable (isSO t = true))

/-- The syntactic objects: the well-formed nonplanar trees over `SOLabel`. -/
def SyntacticObject : Type := { t : Nonplanar SOLabel // IsSO t }

instance : DecidableEq SyntacticObject := Subtype.instDecidableEq

/-! ### The three shapes -/

/-- A lexical leaf. -/
def SyntacticObject.lexLeaf (tok : LIToken) : SyntacticObject := ⟨Nonplanar.leaf (Sum.inl tok), rfl⟩

/-- The trace leaf: a childless bare vertex, the mark an admissible cut leaves in the remaining
    tree ([marcolli-chomsky-berwick-2025], Definition 1.2.6). It carries no index. -/
def SyntacticObject.traceLeaf : SyntacticObject := ⟨Nonplanar.leaf (Sum.inr ()), by decide⟩

/-- A bare binary node is well-formed exactly when both daughters are. -/
theorem isSO_node_pair (a b : Nonplanar SOLabel) :
    isSO (Nonplanar.node (Sum.inr ()) ({a, b} : Multiset (Nonplanar SOLabel)))
      = (isSO a && isSO b) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  show isSO (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = (isSO (Nonplanar.mk pa) && isSO (Nonplanar.mk pb))
  rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
        = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl,
      Nonplanar.node_mk_tree_list]
  simp only [isSO_mk, isSOPlanar, isSOPlanarList, List.length_cons, List.length_nil,
             Nat.reduceAdd, Nat.reduceBEq, Bool.or_true, Bool.true_and, Bool.and_true]

/-- The bare binary node over two syntactic objects: Merge on the carrier, also written `*`.
    Noncomputable, since it goes through the smart constructor `Nonplanar.node`; concrete
    results are built planar-first and related by `node_mk`. -/
noncomputable def SyntacticObject.node (l r : SyntacticObject) : SyntacticObject :=
  ⟨Nonplanar.node (Sum.inr ()) {l.val, r.val}, by
    show isSO (Nonplanar.node (Sum.inr ()) {l.val, r.val}) = true
    have hl : isSO l.val = true := l.2
    have hr : isSO r.val = true := r.2
    rw [isSO_node_pair, hl, hr, Bool.and_self]⟩

@[simp] theorem SyntacticObject.node_val (l r : SyntacticObject) :
    (SyntacticObject.node l r).val = Nonplanar.node (Sum.inr ()) {l.val, r.val} := rfl

/-- A node of two planar-built objects is the planar binary node, so concrete results are
    `decide`-able. -/
theorem SyntacticObject.node_mk (pl pr : RoseTree SOLabel)
    (hl : IsSO (Nonplanar.mk pl)) (hr : IsSO (Nonplanar.mk pr)) :
    (SyntacticObject.node ⟨Nonplanar.mk pl, hl⟩ ⟨Nonplanar.mk pr, hr⟩).val
      = Nonplanar.mk (.node (Sum.inr ()) [pl, pr]) := by
  rw [SyntacticObject.node_val,
      show ({Nonplanar.mk pl, Nonplanar.mk pr} : Multiset (Nonplanar SOLabel))
        = Multiset.ofList ([pl, pr].map Nonplanar.mk) from rfl,
      Nonplanar.node_mk_tree_list]

/-! ### Induction and case analysis -/

/-- The children of a well-formed node are well-formed. -/
theorem isSOPlanar_of_mem {cs : List (RoseTree SOLabel)} (h : isSOPlanarList cs = true) :
    ∀ c ∈ cs, isSOPlanar c = true := by
  induction cs with
  | nil => intro _ hc; exact absurd hc List.not_mem_nil
  | cons hd tl ih =>
    rw [isSOPlanarList, Bool.and_eq_true] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact h.1
    · exact ih h.2 c hmem

/-- Induction on syntactic objects: every syntactic object is a lexical leaf, the trace leaf, or
    a node of two syntactic objects. -/
@[elab_as_elim]
theorem SyntacticObject.ind {motive : SyntacticObject → Prop}
    (lex : ∀ tok, motive (SyntacticObject.lexLeaf tok))
    (trace : motive SyntacticObject.traceLeaf)
    (node : ∀ l r : SyntacticObject, motive l → motive r → motive (SyntacticObject.node l r))
    (s : SyntacticObject) : motive s := by
  suffices H : ∀ n (p : RoseTree SOLabel) (hp : IsSO (Nonplanar.mk p)),
      p.numNodes = n → motive ⟨Nonplanar.mk p, hp⟩ by
    obtain ⟨t, ht⟩ := s
    refine Quotient.inductionOn (motive := fun t => ∀ (ht : IsSO t), motive ⟨t, ht⟩)
      t (fun p ht => H p.numNodes p ht rfl) ht
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rintro ⟨lbl, cs⟩ hp hw
    have hpl : isSOPlanar (RoseTree.node lbl cs) = true := hp
    cases lbl with
    | inl tok =>
      rw [isSOPlanar] at hpl
      rcases cs with _ | ⟨c, cs'⟩
      · exact lex tok
      · simp at hpl
    | inr u =>
      cases u
      rw [isSOPlanar, Bool.and_eq_true] at hpl
      obtain ⟨hlen, hlist⟩ := hpl
      rcases cs with _ | ⟨pl, _ | ⟨pr, _ | ⟨x, rest⟩⟩⟩
      · exact trace
      · simp at hlen
      · have hl : isSOPlanar pl = true := isSOPlanar_of_mem hlist pl (by simp)
        have hr : isSOPlanar pr = true := isSOPlanar_of_mem hlist pr (by simp)
        have hnode : (⟨Nonplanar.mk (RoseTree.node (Sum.inr ()) [pl, pr]), hp⟩ : SyntacticObject)
            = SyntacticObject.node ⟨Nonplanar.mk pl, hl⟩ ⟨Nonplanar.mk pr, hr⟩ :=
          Subtype.ext (SyntacticObject.node_mk pl pr hl hr).symm
        rw [hnode]
        simp only [RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil] at hw
        exact node _ _ (IH pl.numNodes (by omega) pl hl rfl) (IH pr.numNodes (by omega) pr hr rfl)
      · simp at hlen

/-- Every syntactic object is a lexical leaf, the trace leaf, or a node. -/
theorem SyntacticObject.exists_form (s : SyntacticObject) :
    (∃ tok, s = SyntacticObject.lexLeaf tok) ∨ s = SyntacticObject.traceLeaf ∨
      (∃ l r, s = SyntacticObject.node l r) := by
  induction s using SyntacticObject.ind with
  | lex tok => exact Or.inl ⟨tok, rfl⟩
  | trace => exact Or.inr (Or.inl rfl)
  | node l r _ _ => exact Or.inr (Or.inr ⟨l, r, rfl⟩)

end Minimalist
