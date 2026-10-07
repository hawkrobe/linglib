/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Positions
public import Mathlib.Order.Atoms
public import Linglib.Syntax.Command
public import Linglib.Syntax.Minimalist.SyntacticObject.Label
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Positions of planar syntactic objects

The positions of a planar syntactic object, the paths to its vertices, form a rooted tree
(`RoseTree.Positions`). Each carries a term, the subtree there read as a syntactic object: the
terms at the covers of a position are the terms its term immediately contains, and the terms at
the positions below it are the terms its term contains, so c-command by a term occurring once is
c-command from its position. Each position also has a head daughter, the daughter carrying its
raising head, and where the raising head is undefined the daughter the drawing convention of the
embedding makes the head: [marcolli-chomsky-berwick-2025] (Lemma 1.13.5) identify a planar
embedding with a total head function, which extends the raising head.

## Main definitions

* `PlanarSyntacticObject.termAt`: the term at a position.
* `Minimalist.headIndex?`: the head daughter of a planar tree.

## Main statements

* `PlanarSyntacticObject.immediatelyContains_termAt`, `PlanarSyntacticObject.containsOrEq_termAt`:
  terms contain one another as their positions dominate one another.
* `PlanarSyntacticObject.cCommandsIn_termAt_iff`: c-command by a term occurring once is c-command
  from its position.
* `Minimalist.exists_headIndex?_of_treeRaisingHead`: the head daughter carries the raising head
  wherever there is one.

## Implementation notes

* The drawing convention puts specifiers to the left of their heads and heads to the left of their
  complements: a left leaf that selects nothing is a specifier and the right daughter heads, a left
  leaf that selects is the head, and otherwise the right daughter heads. It decides only where the
  raising head is undefined, at a phrase merged in place beside another phrase, which
  [chomsky-2013] labels by features the two share.

## TODO

* The positions at or below the maximal projection of a head occurring once carry exactly the
  terms within its projection, where the raising head is defined along the projection line.

## References

* [marcolli-chomsky-berwick-2025]
* [chomsky-2013]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order PhraseStructure

/-! ### Terms at positions -/

namespace PlanarSyntacticObject

open RoseTree SyntacticObject

variable {t : PlanarSyntacticObject} {p : t.val.Positions} {y : SyntacticObject}

theorem isSyntacticObject_subtree (p : t.val.Positions) :
    IsSyntacticObject (UnorderedTree.mk p.subtree) :=
  isSyntacticObject_of_mem_subtrees t.toSyntacticObject _
    (mem_unorderedSubtrees.2 ⟨_, _, p.subtreeAt_eq, rfl⟩)

variable (t) in
/-- The term of `t` at a position. -/
def termAt (p : t.val.Positions) : SyntacticObject := ⟨_, isSyntacticObject_subtree p⟩

@[simp] theorem termAt_bot : t.termAt ⊥ = t.toSyntacticObject := rfl

/-- The term at a position immediately contains the terms at its covers. -/
theorem immediatelyContains_termAt :
    immediatelyContains (t.termAt p) y ↔ ∃ q, p ⋖ q ∧ t.termAt q = y := by
  show y.val ∈ (UnorderedTree.mk p.subtree).children ↔ _
  rw [UnorderedTree.children_mk, Multiset.mem_coe, List.mem_map]
  constructor
  · rintro ⟨c, hc, hcy⟩
    obtain ⟨q, hpq, rfl⟩ := Positions.mem_children_subtree.1 hc
    exact ⟨q, hpq, Subtype.ext hcy⟩
  · rintro ⟨q, hpq, rfl⟩
    exact ⟨q.subtree, Positions.mem_children_subtree.2 ⟨q, hpq, rfl⟩, rfl⟩

/-- The term at a position contains or equals the terms at the positions below it. -/
theorem containsOrEq_termAt : containsOrEq (t.termAt p) y ↔ ∃ q, p ≤ q ∧ t.termAt q = y := by
  rw [← mem_terms, ← Multiset.mem_map_of_injective Subtype.val_injective, map_val_terms]
  show y.val ∈ unorderedSubtrees p.subtree ↔ _
  simp only [unorderedSubtrees_eq_map, Multiset.mem_coe, List.mem_map, mem_subtrees,
    Positions.isSubtree_subtree]
  constructor
  · rintro ⟨s, ⟨q, hpq, rfl⟩, hsy⟩
    exact ⟨q, hpq, Subtype.ext hsy⟩
  · rintro ⟨q, hpq, rfl⟩
    exact ⟨q.subtree, ⟨q, hpq, rfl⟩, rfl⟩

/-- The terms of a planar object are the terms at its positions. -/
theorem mem_terms_iff : y ∈ t.toSyntacticObject.terms ↔ ∃ q, t.termAt q = y := by
  rw [mem_terms, ← termAt_bot, containsOrEq_termAt]
  simp



variable {a : t.val.Positions} {x : SyntacticObject}

/-- In a syntactic object the parent of a position other than the root branches. -/
theorem isBranchingAt_parent (ha : a ≠ ⊥) : IsBranchingAt t.val a.val.parent := by
  have hc : a.subtree ∈ (Order.pred a).subtree.children :=
    Positions.mem_children_subtree.2
      ⟨a, Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using ha), rfl⟩
  have hso := isSyntacticObject_subtree (Order.pred a)
  refine mem_positionsWhere.2 ⟨_, (Order.pred a).subtreeAt_eq, ?_⟩
  generalize (Order.pred a).subtree = s at hc hso
  obtain ⟨v, cs⟩ := s
  rcases length_eq_zero_or_two hso with h0 | h2 <;>
    grind [arity, List.length_eq_zero_iff, children_node]

/-- C-command by a term occurring only at `a` is c-command from `a`. -/
theorem cCommandsIn_termAt_iff (hu : ∀ q, t.termAt q = t.termAt a → q = a) :
    t.toSyntacticObject.cCommandsIn (t.termAt a) x ↔
      ∃ q : t.val.Positions, CCommands t.val a q ∧ t.termAt q = x := by
  constructor
  · rintro ⟨z, -, ⟨w, hw, haw, hwz, hne⟩, hzx⟩
    obtain ⟨m, rfl⟩ := mem_terms_iff.1 hw
    obtain ⟨c, hmc, hca⟩ := immediatelyContains_termAt.1 haw
    obtain ⟨d, hmd, rfl⟩ := immediatelyContains_termAt.1 hwz
    obtain ⟨q, hdq, rfl⟩ := containsOrEq_termAt.1 hzx
    obtain rfl := hu c hca
    have ha : c ≠ ⊥ := ne_bot_of_gt hmc.lt
    have hm : m.val = c.val.parent := by rw [← Positions.pred_val, Order.pred_eq_of_covBy hmc]
    refine ⟨q, (cCommands_iff_parent_lt (fun h ↦ ha (Subtype.ext h)) (isBranchingAt_parent ha)).2
      ⟨hm ▸ Subtype.coe_lt_coe.2 (hmd.lt.trans_le hdq), fun hcq ↦ hne ?_⟩, rfl⟩
    have hcd : c = d := by
      rcases IsLeftLinear.comparable_of_le_common hcq (Subtype.coe_le_coe.2 hdq) with h | h
      · exact (hmd.eq_or_eq hmc.le (Subtype.coe_le_coe.1 h)).resolve_left hmc.ne'
      · exact ((hmc.eq_or_eq hmd.le (Subtype.coe_le_coe.1 h)).resolve_left hmd.ne').symm
    rw [hcd]
  · rintro ⟨q, hq, rfl⟩
    have ha : a ≠ ⊥ := fun h ↦ hq.2.1 (h ▸ bot_le)
    obtain ⟨hpq, haq⟩ :=
      (cCommands_iff_parent_lt (fun h ↦ ha (Subtype.ext h)) (isBranchingAt_parent ha)).1 hq
    obtain ⟨d, hpd, hdq⟩ := exists_covBy_le_of_lt (show Order.pred a < q from hpq)
    refine ⟨t.termAt d, mem_terms_iff.2 ⟨d, rfl⟩, ⟨_, mem_terms_iff.2 ⟨Order.pred a, rfl⟩,
      immediatelyContains_termAt.2
        ⟨a, Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using ha), rfl⟩,
      immediatelyContains_termAt.2 ⟨d, hpd, rfl⟩, fun h ↦ ?_⟩, containsOrEq_termAt.2 ⟨q, hdq, rfl⟩⟩
    obtain rfl := hu d h.symm
    exact haq hdq

/-- A term immediately containing the term at `a`, which occurs only there, is the term at its
parent. -/
theorem eq_termAt_pred_of_immediatelyContains (hu : ∀ q, t.termAt q = t.termAt a → q = a)
    {m : SyntacticObject} (hm : m ∈ t.toSyntacticObject.terms)
    (h : immediatelyContains m (t.termAt a)) : m = t.termAt (Order.pred a) := by
  obtain ⟨m, rfl⟩ := mem_terms_iff.1 hm
  obtain ⟨c, hmc, hca⟩ := immediatelyContains_termAt.1 h
  obtain rfl := hu c hca
  rw [Order.pred_eq_of_covBy hmc]

end PlanarSyntacticObject

/-! ### Head daughters -/

/-- The raising head of a planar tree, that of its unordered image. -/
def treeRaisingHead (s : RoseTree Vertex) : Option LIToken :=
  (liftN (fun tok ↦ (⟨.sel (.of tok tok.item.outerSel), 0⟩ : RaisingState)) raisingTraceState
    (UnorderedTree.mk s)).label.label

theorem treeRaisingHead_subtree {t : PlanarSyntacticObject} (p : t.val.Positions) :
    treeRaisingHead p.subtree = (t.termAt p).raisingHead := rfl

/-- The drawing convention makes a token or trace leaf its own head; at a binary node it takes a
left leaf that selects nothing for a specifier and looks for the head in the right daughter, takes
a left leaf that selects for the head, and otherwise looks in the right daughter. This is the
head path it assigns. -/
def conventionHeadPos? : RoseTree Vertex → Option (List ℕ)
  | .node (.inl (some _)) _ | .node (.inr (some _)) _ => some []
  | .node (.inl none) [.node (.inl (some tok)) [], r] =>
      if tok.item.outerSel = [] then (conventionHeadPos? r).map (1 :: ·) else some [0]
  | .node (.inl none) [_, r] => (conventionHeadPos? r).map (1 :: ·)
  | .node (.inl none) _ => none
  | .node (.inr none) _ => none

/-- The head daughter of a planar tree is the first daughter carrying its raising head, and where
it has none, the first step of the drawing convention's head path. -/
def headIndex? (s : RoseTree Vertex) : Option ℕ :=
  ((treeRaisingHead s).bind fun h ↦ s.children.findIdx? (treeRaisingHead · = some h)) <|>
    (conventionHeadPos? s).bind List.head?

/-- Where a planar syntactic object with daughters has a raising head, its head daughter carries
it. -/
theorem exists_headIndex?_of_treeRaisingHead {s : RoseTree Vertex} {ℓ : LIToken}
    (hs : IsSyntacticObject (UnorderedTree.mk s)) (hc : s.children ≠ [])
    (h : treeRaisingHead s = some ℓ) :
    ∃ i c, headIndex? s = some i ∧ s.children[i]? = some c ∧ treeRaisingHead c = some ℓ := by
  obtain ⟨v, cs⟩ := s
  obtain rfl := eq_bare_of_ne_nil hs hc
  obtain ⟨l, r, rfl⟩ : ∃ l r, cs = [l, r] :=
    List.length_eq_two.1 ((length_eq_zero_or_two hs).resolve_left fun h0 ↦
      hc (List.length_eq_zero_iff.1 h0))
  obtain ⟨hl, hr⟩ := (isSyntacticObject_mk_merge l r).1 hs
  have hm : treeRaisingHead (.node Vertex.bare [l, r]) = (merge ⟨_, hl⟩ ⟨_, hr⟩).raisingHead := by
    simp only [raisingHead, raisingCheck, liftFun, merge_mk]; rfl
  by_cases hl' : treeRaisingHead l = some ℓ
  · exact ⟨0, l, by simp [headIndex?, h, hl', List.findIdx?_cons], rfl, hl'⟩
  · have hr' : treeRaisingHead r = some ℓ :=
      (raisingHead_merge (l := ⟨_, hl⟩) (r := ⟨_, hr⟩) (hm ▸ h)).resolve_left fun h' ↦ hl' h'
    exact ⟨1, r, by simp [headIndex?, h, hl', hr', List.findIdx?_cons], rfl, hr'⟩

end Minimalist
