/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Subterm enumeration and containment for syntactic objects

[marcolli-chomsky-berwick-2025] §1.1–1.2. The containment / subterm theory of the
`SyntacticObject` carrier, mirroring the legacy `Basic.lean` theory on
`FreeCommMagma (LIToken ⊕ Nat)`. Imports only the carrier skeleton (no Merge algebra).

## Contents
- `SyntacticObject.immediatelyContains` — membership in the root children (via
`Nonplanar.rootChildren`).
- `SyntacticObject.subtrees`/`SyntacticObject.Acc` — subterm enumeration (incl. root) and MCB's
accessible terms
  `Acc(T)` (Def 1.2.2, root excluded).
- `SyntacticObject.contains`/`isTermOf`/`containsOrEq` — dominance and its reflexive/term-of
variants.
- subtree ↔ containment bridges, and tree-relative c-command (`cCommandsIn`).
-/

namespace Minimalist

open RootedTree

/-! ### Immediate containment (via `Nonplanar.rootChildren`) -/

/-- `x` **immediately contains** `y`: `y` is one of `x`'s root daughters
    ([marcolli-chomsky-berwick-2025] §1.1; Definition 13 of the legacy theory). -/
def SyntacticObject.immediatelyContains (x y : SyntacticObject) : Prop :=
  y.val ∈ Nonplanar.rootChildren x.val

instance (x y : SyntacticObject) : Decidable (SyntacticObject.immediatelyContains x y) :=
  inferInstanceAs (Decidable (_ ∈ _))

@[simp] theorem SyntacticObject.immediatelyContains_lexLeaf (tok : LIToken) (y : SyntacticObject) :
    ¬ SyntacticObject.immediatelyContains (SyntacticObject.lexLeaf tok) y := by
  simp only [SyntacticObject.immediatelyContains, SyntacticObject.lexLeaf, Nonplanar.leaf,
    Nonplanar.rootChildren_mk, RoseTree.leaf, RoseTree.children, List.map_nil, Multiset.coe_nil,
    Multiset.notMem_zero, not_false_iff]

@[simp] theorem SyntacticObject.immediatelyContains_traceLeaf (y : SyntacticObject) :
    ¬ SyntacticObject.immediatelyContains SyntacticObject.traceLeaf y := by
  simp only [SyntacticObject.immediatelyContains, SyntacticObject.traceLeaf, Nonplanar.leaf,
    Nonplanar.rootChildren_mk, RoseTree.leaf, RoseTree.children, List.map_nil, Multiset.coe_nil,
    Multiset.notMem_zero, not_false_iff]

@[simp] theorem SyntacticObject.immediatelyContains_node (l r y : SyntacticObject) :
    SyntacticObject.immediatelyContains (SyntacticObject.node l r) y ↔ y = l ∨ y = r := by
  rw [SyntacticObject.immediatelyContains, SyntacticObject.node_val, Nonplanar.rootChildren_node,
      Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
  exact ⟨fun h => h.imp Subtype.ext Subtype.ext,
         fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val)⟩

/-! ### Subterm enumeration

`Nonplanar.rootChildren` is single-level, so deep enumeration is built fresh at the
planar level and lifted. The result is a multiset of *nonplanar* subtrees; its
`Perm`-invariance lets it descend to the quotient. -/

mutual
/-- All subtrees of a planar tree (incl. the root), as nonplanar trees. -/
def subtreesNPlanar : RoseTree SOLabel → Multiset (Nonplanar SOLabel)
  | .node a cs => Nonplanar.mk (.node a cs) ::ₘ subtreesNPlanarList cs
/-- Auxiliary: union of subtree-multisets across a child list. -/
def subtreesNPlanarList : List (RoseTree SOLabel) → Multiset (Nonplanar SOLabel)
  | []      => 0
  | c :: cs => subtreesNPlanar c + subtreesNPlanarList cs
end

mutual
/-- `subtreesNPlanar` is `Perm`-invariant, so it descends to `Nonplanar`. At a node the
    root `mk`-image is fixed by `mk_eq_mk_iff` and the child-list sum by the `PermList`
    companion. -/
theorem subtreesNPlanar_perm : ∀ {t s : RoseTree SOLabel}, RoseTree.Perm t s →
    subtreesNPlanar t = subtreesNPlanar s
  | _, _, .node h => by
    simp only [subtreesNPlanar]
    rw [Nonplanar.mk_eq_mk_iff.mpr (RoseTree.Perm.node h), subtreesNPlanarList_permList h]
  | _, _, .trans h₁ h₂ => (subtreesNPlanar_perm h₁).trans (subtreesNPlanar_perm h₂)

/-- The child-list subtree sum is `PermList`-invariant: it is a multiset sum, and the
    `List.Perm`-style case split matches heads by the mutual `subtreesNPlanar_perm` and
    reorders by `add_left_comm`. -/
theorem subtreesNPlanarList_permList : ∀ {cs ds : List (RoseTree SOLabel)},
    RoseTree.PermList cs ds → subtreesNPlanarList cs = subtreesNPlanarList ds
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [subtreesNPlanarList, subtreesNPlanar_perm h, subtreesNPlanarList_permList hs]
  | _, _, .swap _ _ _ => by simp only [subtreesNPlanarList]; rw [add_left_comm]
  | _, _, .trans h₁ h₂ =>
    (subtreesNPlanarList_permList h₁).trans (subtreesNPlanarList_permList h₂)
end

/-- All subtrees of a nonplanar tree (incl. the root). -/
def subtreesN : Nonplanar SOLabel → Multiset (Nonplanar SOLabel) :=
  Nonplanar.lift subtreesNPlanar (fun _ _ h => subtreesNPlanar_perm h)

@[simp] theorem subtreesN_mk (t : RoseTree SOLabel) :
    subtreesN (Nonplanar.mk t) = subtreesNPlanar t := rfl

theorem subtreesN_leaf (a : SOLabel) : subtreesN (Nonplanar.leaf a) = {Nonplanar.leaf a} := by
  show subtreesNPlanar (RoseTree.leaf a) = _
  simp only [RoseTree.leaf, subtreesNPlanar, subtreesNPlanarList]
  rfl

/-- `subtreesN` on a bare binary node: the node plus the subtrees of each child. -/
theorem subtreesN_node (a b : Nonplanar SOLabel) :
    subtreesN (Nonplanar.node (Sum.inr ()) {a, b})
      = Nonplanar.node (Sum.inr ()) {a, b} ::ₘ (subtreesN a + subtreesN b) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (RoseTree.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl,
        Nonplanar.node_mk_tree_list]
  show subtreesN (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
        ::ₘ (subtreesN (Nonplanar.mk pa) + subtreesN (Nonplanar.mk pb))
  simp only [key, subtreesN_mk, subtreesNPlanar, subtreesNPlanarList, add_zero]

/-- Membership in `subtreesN` of a leaf. -/
@[simp] theorem mem_subtreesN_leaf {m : Nonplanar SOLabel} {a : SOLabel} :
    m ∈ subtreesN (Nonplanar.leaf a) ↔ m = Nonplanar.leaf a := by
  rw [subtreesN_leaf, Multiset.mem_singleton]

/-- Membership in `subtreesN` of a bare binary node. -/
@[simp] theorem mem_subtreesN_node {m a b : Nonplanar SOLabel} :
    m ∈ subtreesN (Nonplanar.node (Sum.inr ()) {a, b})
      ↔ m = Nonplanar.node (Sum.inr ()) {a, b} ∨ m ∈ subtreesN a ∨ m ∈ subtreesN b := by
  rw [subtreesN_node, Multiset.mem_cons, Multiset.mem_add]

/-- Every nonplanar tree is among its own subtrees. -/
theorem self_mem_subtreesN (u : Nonplanar SOLabel) : u ∈ subtreesN u := by
  refine Quotient.inductionOn u fun p => ?_
  obtain ⟨lbl, cs⟩ := p
  show Nonplanar.mk (RoseTree.node lbl cs) ∈ subtreesNPlanar (RoseTree.node lbl cs)
  rw [subtreesNPlanar]; exact Multiset.mem_cons_self _ _

/-! ### `SyntacticObject.subtrees` / `SyntacticObject.Acc` -/

/-- Subtrees of a syntactic object are themselves syntactic objects. -/
theorem subtreesN_closure (s : SyntacticObject) : ∀ m ∈ subtreesN s.val, IsSO m := by
  induction s using SyntacticObject.ind with
  | lex tok =>
    intro m hm
    rw [show (SyntacticObject.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl,
        mem_subtreesN_leaf] at hm
    subst hm; exact (SyntacticObject.lexLeaf tok).2
  | trace =>
    intro m hm
    rw [show SyntacticObject.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl,
        mem_subtreesN_leaf] at hm
    subst hm; exact SyntacticObject.traceLeaf.2
  | node l r ihl ihr =>
    intro m hm
    rw [SyntacticObject.node_val, mem_subtreesN_node] at hm
    rcases hm with rfl | hl | hr
    · exact (SyntacticObject.node l r).2
    · exact ihl m hl
    · exact ihr m hr

/-- All subtrees of a syntactic object (incl. the root), as syntactic objects
    ([marcolli-chomsky-berwick-2025] §1.2; the legacy `SyntacticObject.subtrees`). -/
def SyntacticObject.subtrees (s : SyntacticObject) : Multiset SyntacticObject :=
  (subtreesN s.val).pmap (fun m h => ⟨m, h⟩) (subtreesN_closure s)

@[simp] theorem SyntacticObject.mem_subtrees {x s : SyntacticObject} :
    x ∈ s.subtrees ↔ x.val ∈ subtreesN s.val := by
  rw [SyntacticObject.subtrees, Multiset.mem_pmap]
  constructor
  · rintro ⟨m, hm, he⟩; rw [← he]; exact hm
  · intro h; exact ⟨x.val, h, Subtype.ext rfl⟩

/-- The root is among its own subtrees. -/
theorem SyntacticObject.self_mem_subtrees (s : SyntacticObject) : s ∈ s.subtrees := by
  rw [SyntacticObject.mem_subtrees]; exact self_mem_subtreesN s.val

/-- Subtree membership at a bare binary node: the node itself, or a subtree of a
    daughter. -/
@[simp] theorem SyntacticObject.mem_subtrees_node {x l r : SyntacticObject} :
    x ∈ (SyntacticObject.node l r).subtrees ↔
      x = SyntacticObject.node l r ∨ x ∈ l.subtrees ∨ x ∈ r.subtrees := by
  rw [SyntacticObject.mem_subtrees, SyntacticObject.node_val, mem_subtreesN_node,
      ← SyntacticObject.mem_subtrees, ← SyntacticObject.mem_subtrees]
  exact Iff.or ⟨fun h => Subtype.ext h, fun h => by rw [h, SyntacticObject.node_val]⟩ Iff.rfl

/-- `subtrees` is downward-closed along the subtree relation: every subtree of a
    subtree of `s` is a subtree of `s`. -/
theorem SyntacticObject.subtrees_subset_of_mem {w s : SyntacticObject} (h : w ∈ s.subtrees) :
    w.subtrees ⊆ s.subtrees := by
  induction s using SyntacticObject.ind with
  | lex tok =>
    rw [SyntacticObject.mem_subtrees,
        show (SyntacticObject.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl,
        mem_subtreesN_leaf] at h
    rw [(Subtype.ext h : w = SyntacticObject.lexLeaf tok)]; exact Multiset.Subset.refl _
  | trace =>
    rw [SyntacticObject.mem_subtrees,
        show SyntacticObject.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl,
        mem_subtreesN_leaf] at h
    rw [(Subtype.ext h : w = SyntacticObject.traceLeaf)]; exact Multiset.Subset.refl _
  | node l r ihl ihr =>
    rw [SyntacticObject.mem_subtrees_node] at h
    rcases h with rfl | hl | hr
    · exact Multiset.Subset.refl _
    · intro z hz; rw [SyntacticObject.mem_subtrees_node]; exact Or.inr (Or.inl (ihl hl hz))
    · intro z hz; rw [SyntacticObject.mem_subtrees_node]; exact Or.inr (Or.inr (ihr hr hz))

/-! ### Cardinality (MCB's vertex/accessible-term counts, Def 1.2.2 eq. 1.2.5) -/

mutual
/-- `subtreesN` has one element per vertex: its cardinality is the node count. -/
theorem subtreesNPlanar_card (p : RoseTree SOLabel) :
    (subtreesNPlanar p).card = p.numNodes := by
  obtain ⟨a, cs⟩ := p
  rw [subtreesNPlanar, Multiset.card_cons, subtreesNPlanarList_card, RoseTree.numNodes_node]; omega
/-- Auxiliary list version. -/
theorem subtreesNPlanarList_card (cs : List (RoseTree SOLabel)) :
    (subtreesNPlanarList cs).card = (cs.map RoseTree.numNodes).sum := by
  match cs with
  | [] => rfl
  | c :: cs => rw [subtreesNPlanarList, Multiset.card_add, subtreesNPlanar_card,
                   subtreesNPlanarList_card, List.map_cons, List.sum_cons]
end

theorem subtreesN_card (u : Nonplanar SOLabel) :
    (subtreesN u).card = Nonplanar.numNodes u :=
  Quotient.inductionOn u subtreesNPlanar_card

/-- **`subtrees` enumerates the vertices** ([marcolli-chomsky-berwick-2025] Def 1.2.2:
    `subtrees = Acc'(T)`, so its size is `#V(T)`, the MCB workspace-size primitive). -/
theorem SyntacticObject.subtrees_card (s : SyntacticObject) :
    (s.subtrees).card = Nonplanar.numNodes s.val := by
  rw [SyntacticObject.subtrees, Multiset.card_pmap, subtreesN_card]

/-! ### Accessible terms `Acc(T)` (Def 1.2.2) -/

/-- MCB's accessible-terms operator `Acc(T)` ([marcolli-chomsky-berwick-2025]
    Def 1.2.2, eq. 1.2.2): the subtrees at **all non-root vertices** (leaves
    included — the counting identity eq. 1.2.5 `#V = b₀ + #Acc` forces this).
    Defined as `subtrees − {self}` (`Acc'(T) = {T} ∪ Acc(T)`, eq. 1.2.3). -/
def SyntacticObject.Acc (s : SyntacticObject) : Multiset SyntacticObject := s.subtrees - {s}

/-- **MCB counting identity** (eq. 1.2.5, one-component case): `#Acc(T) = #V(T) − 1`. -/
theorem SyntacticObject.Acc_card (s : SyntacticObject) :
    (s.Acc).card = Nonplanar.numNodes s.val - 1 := by
  rw [SyntacticObject.Acc,
      Multiset.card_sub (Multiset.singleton_le.mpr (SyntacticObject.self_mem_subtrees s)),
      SyntacticObject.subtrees_card, Multiset.card_singleton]

@[simp] theorem SyntacticObject.Acc_lexLeaf (tok : LIToken) :
    (SyntacticObject.lexLeaf tok).Acc = 0 := by
  rw [← Multiset.card_eq_zero, SyntacticObject.Acc_card,
      show (SyntacticObject.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl,
      Nonplanar.numNodes_leaf]

@[simp] theorem SyntacticObject.Acc_traceLeaf : SyntacticObject.traceLeaf.Acc = 0 := by
  rw [← Multiset.card_eq_zero, SyntacticObject.Acc_card,
      show SyntacticObject.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl,
      Nonplanar.numNodes_leaf]

/-! ### Containment / dominance -/

/-- Weight of a bare binary node is one more than the sum of its daughters'. -/
theorem weight_node_pair (a b : Nonplanar SOLabel) :
    Nonplanar.numNodes (Nonplanar.node (Sum.inr ()) {a, b})
      = Nonplanar.numNodes a + Nonplanar.numNodes b + 1 := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (RoseTree.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]
  show Nonplanar.numNodes (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = Nonplanar.numNodes (Nonplanar.mk pa) + Nonplanar.numNodes (Nonplanar.mk pb) + 1
  rw [key]
  show (RoseTree.node (Sum.inr ()) [pa, pb]).numNodes = pa.numNodes + pb.numNodes + 1
  simp only [RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega

/-- **Containment (dominance)** is the transitive closure of immediate containment
    ([marcolli-chomsky-berwick-2025] §1.1; the legacy `contains`). -/
inductive SyntacticObject.contains : SyntacticObject → SyntacticObject → Prop
  | imm : ∀ x y, SyntacticObject.immediatelyContains x y → SyntacticObject.contains x y
  | trans : ∀ x y z, SyntacticObject.immediatelyContains x z → SyntacticObject.contains z y →
      SyntacticObject.contains x y

theorem SyntacticObject.imm_implies_contains {x y : SyntacticObject}
    (h : SyntacticObject.immediatelyContains x y) : SyntacticObject.contains x y := .imm x y h

theorem SyntacticObject.contains_trans {x y z : SyntacticObject}
    (hxy : SyntacticObject.contains x y) (hyz : SyntacticObject.contains y z) :
    SyntacticObject.contains x z := by
  induction hxy with
  | imm x y himm => exact .trans x z y himm hyz
  | trans x y w himm _ ih => exact .trans x z w himm (ih hyz)

/-- Immediate containment strictly decreases weight. -/
theorem SyntacticObject.immediatelyContains_lt_weight {x y : SyntacticObject}
    (h : SyntacticObject.immediatelyContains x y) :
    Nonplanar.numNodes y.val < Nonplanar.numNodes x.val := by
  rcases SyntacticObject.exists_form x with ⟨tok, rfl⟩ | rfl | ⟨l, r, rfl⟩
  · exact absurd h (SyntacticObject.immediatelyContains_lexLeaf tok y)
  · exact absurd h (SyntacticObject.immediatelyContains_traceLeaf y)
  · rw [SyntacticObject.immediatelyContains_node] at h
    rw [SyntacticObject.node_val, weight_node_pair]
    rcases h with rfl | rfl <;> omega

/-- Containment strictly decreases weight; hence it is irreflexive. -/
theorem SyntacticObject.contains_lt_weight {x y : SyntacticObject}
    (h : SyntacticObject.contains x y) :
    Nonplanar.numNodes y.val < Nonplanar.numNodes x.val := by
  induction h with
  | imm _ _ himm => exact SyntacticObject.immediatelyContains_lt_weight himm
  | trans _ _ _ himm _ ih => exact lt_trans ih (SyntacticObject.immediatelyContains_lt_weight himm)

theorem SyntacticObject.contains_irrefl (x : SyntacticObject) : ¬ SyntacticObject.contains x x :=
  fun h => absurd (SyntacticObject.contains_lt_weight h) (lt_irrefl _)

/-! ### Subtree ↔ containment bridge -/

theorem SyntacticObject.mem_subtrees_of_immediatelyContains {x y : SyntacticObject}
    (h : SyntacticObject.immediatelyContains x y) :
    y ∈ x.subtrees := by
  rcases SyntacticObject.exists_form x with ⟨tok, rfl⟩ | rfl | ⟨l, r, rfl⟩
  · exact absurd h (SyntacticObject.immediatelyContains_lexLeaf tok y)
  · exact absurd h (SyntacticObject.immediatelyContains_traceLeaf y)
  · rw [SyntacticObject.immediatelyContains_node] at h
    rcases h with heq | heq
    · rw [heq, SyntacticObject.mem_subtrees_node]
      exact Or.inr (Or.inl (SyntacticObject.self_mem_subtrees l))
    · rw [heq, SyntacticObject.mem_subtrees_node]
      exact Or.inr (Or.inr (SyntacticObject.self_mem_subtrees r))

theorem SyntacticObject.mem_subtrees_of_contains {x y : SyntacticObject}
    (h : SyntacticObject.contains x y) : y ∈ x.subtrees := by
  induction h with
  | imm x y himm => exact SyntacticObject.mem_subtrees_of_immediatelyContains himm
  | trans x y w himm _ ih =>
    exact SyntacticObject.subtrees_subset_of_mem
      (SyntacticObject.mem_subtrees_of_immediatelyContains himm) ih

/-- A subtree of `x` is either `x` itself or properly contained in `x`. -/
theorem SyntacticObject.mem_subtrees_iff_eq_or_contains {x y : SyntacticObject} :
    y ∈ x.subtrees ↔ y = x ∨ SyntacticObject.contains x y := by
  refine ⟨fun h => ?_, fun h => h.elim (fun he => he ▸ SyntacticObject.self_mem_subtrees x)
    SyntacticObject.mem_subtrees_of_contains⟩
  induction x using SyntacticObject.ind with
  | lex tok =>
    rw [SyntacticObject.mem_subtrees,
        show (SyntacticObject.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl,
        mem_subtreesN_leaf] at h
    exact Or.inl (Subtype.ext h)
  | trace =>
    rw [SyntacticObject.mem_subtrees,
        show SyntacticObject.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl,
        mem_subtreesN_leaf] at h
    exact Or.inl (Subtype.ext h)
  | node l r ihl ihr =>
    rw [SyntacticObject.mem_subtrees_node] at h
    rcases h with rfl | hl | hr
    · exact Or.inl rfl
    · refine Or.inr ?_
      rcases ihl hl with heq | hc
      · rw [heq]; exact .imm _ _ ((SyntacticObject.immediatelyContains_node l r l).mpr (Or.inl rfl))
      · exact .trans _ _ l ((SyntacticObject.immediatelyContains_node l r l).mpr (Or.inl rfl)) hc
    · refine Or.inr ?_
      rcases ihr hr with heq | hc
      · rw [heq]; exact .imm _ _ ((SyntacticObject.immediatelyContains_node l r r).mpr (Or.inr rfl))
      · exact .trans _ _ r ((SyntacticObject.immediatelyContains_node l r r).mpr (Or.inr rfl)) hc

/-- **Containment ↔ proper subtree membership.** Gives a decision procedure for
    `contains` without well-founded recursion: `y` is properly contained in `x` iff
    it is a subtree distinct from `x`. -/
theorem SyntacticObject.contains_iff_mem_subtrees_and_ne {x y : SyntacticObject} :
    SyntacticObject.contains x y ↔ y ∈ x.subtrees ∧ y ≠ x := by
  constructor
  · intro h
    exact ⟨SyntacticObject.mem_subtrees_of_contains h,
      fun he => SyntacticObject.contains_irrefl x (he ▸ h)⟩
  · rintro ⟨hmem, hne⟩
    rcases SyntacticObject.mem_subtrees_iff_eq_or_contains.mp hmem with rfl | hc
    · exact absurd rfl hne
    · exact hc

instance (x y : SyntacticObject) : Decidable (SyntacticObject.contains x y) :=
  decidable_of_iff _ SyntacticObject.contains_iff_mem_subtrees_and_ne.symm

/-! ### Term-of and reflexive containment -/

/-- `x` is a **term of** `y`: `x = y` or `y` contains `x`. -/
def SyntacticObject.isTermOf (x y : SyntacticObject) : Prop := x = y ∨ SyntacticObject.contains y x

instance (x y : SyntacticObject) : Decidable (SyntacticObject.isTermOf x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem SyntacticObject.isTermOf_iff_mem_subtrees (x y : SyntacticObject) :
    SyntacticObject.isTermOf x y ↔ x ∈ y.subtrees :=
  SyntacticObject.mem_subtrees_iff_eq_or_contains.symm

/-- Reflexive containment. -/
def SyntacticObject.containsOrEq (x y : SyntacticObject) : Prop :=
  x = y ∨ SyntacticObject.contains x y

instance (x y : SyntacticObject) : Decidable (SyntacticObject.containsOrEq x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem SyntacticObject.containsOrEq_trans {x y z : SyntacticObject}
    (hxy : SyntacticObject.containsOrEq x y) (hyz : SyntacticObject.containsOrEq y z) :
    SyntacticObject.containsOrEq x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  · rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (SyntacticObject.contains_trans hxy hyz)

/-! ### RoseTree-relative c-command ([reinhart-1976]) -/

/-- `x` and `y` are **sisters in** `root`: distinct co-daughters of some subtree. -/
def SyntacticObject.areSistersIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.subtrees,
    SyntacticObject.immediatelyContains z x ∧ SyntacticObject.immediatelyContains z y ∧ x ≠ y

instance (root x y : SyntacticObject) : Decidable (SyntacticObject.areSistersIn root x y) :=
  Multiset.decidableExistsMultiset

/-- `x` **c-commands** `y` in `root`: `x` has a sister (in `root`) that
    contains-or-equals `y`. -/
def SyntacticObject.cCommandsIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.subtrees, SyntacticObject.areSistersIn root x z ∧ SyntacticObject.containsOrEq z y

instance (root x y : SyntacticObject) : Decidable (SyntacticObject.cCommandsIn root x y) :=
  Multiset.decidableExistsMultiset

/-- `x` **asymmetrically** c-commands `y` in `root`. -/
def SyntacticObject.asymCCommandsIn (root x y : SyntacticObject) : Prop :=
  SyntacticObject.cCommandsIn root x y ∧ ¬ SyntacticObject.cCommandsIn root y x

instance (root x y : SyntacticObject) : Decidable (SyntacticObject.asymCCommandsIn root x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### `decide` demonstrations

The containment / c-command decision procedures reduce on concrete trees built
via `Nonplanar.mk ∘ RoseTree.node` (not the noncomputable `SyntacticObject.node`), confirming the
"state result trees directly" discipline carries through to the relational layer. -/

private def demoL : SyntacticObject :=
  ⟨Nonplanar.mk (.node (Sum.inl (mkTraceToken 0)) []), by decide⟩
private def demoR : SyntacticObject :=
  ⟨Nonplanar.mk (.node (Sum.inl (mkTraceToken 1)) []), by decide⟩
private def demoT : SyntacticObject :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl (mkTraceToken 0)) [], .node (Sum.inl (mkTraceToken 1)) []]), by decide⟩

/-- The root properly contains its left daughter; the daughter does not contain the root. -/
example : SyntacticObject.contains demoT demoL ∧ ¬ SyntacticObject.contains demoL demoT := by decide
/-- The two daughters c-command each other in the root. -/
example : SyntacticObject.cCommandsIn demoT demoL demoR := by decide
/-- A node has one more vertex than the sum of its daughters' (eq. 1.2.5 witness). -/
example : (demoT.subtrees).card = 3 := by decide

end Minimalist
