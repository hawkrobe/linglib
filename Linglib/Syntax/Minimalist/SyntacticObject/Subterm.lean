/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject

/-!
# Subterm enumeration and containment for syntactic objects

[marcolli-chomsky-berwick-2025] §1.1–1.2. The containment / subterm theory of the
`SO` carrier, mirroring the legacy `Basic.lean` theory on
`FreeCommMagma (LIToken ⊕ Nat)`. Imports only the carrier skeleton (no Merge algebra).

## Contents
- `SO.immediatelyContains` — membership in the root children (via `Nonplanar.rootChildren`).
- `SO.subtrees`/`SO.Acc` — subterm enumeration (incl. root) and MCB's accessible terms
  `Acc(T)` (Def 1.2.2, root excluded).
- `SO.contains`/`isTermOf`/`containsOrEq` — dominance and its reflexive/term-of variants.
- subtree ↔ containment bridges, and tree-relative c-command (`cCommandsIn`).
-/

namespace Minimalist

open RootedTree

/-! ### Immediate containment (via `Nonplanar.rootChildren`) -/

/-- `x` **immediately contains** `y`: `y` is one of `x`'s root daughters
    ([marcolli-chomsky-berwick-2025] §1.1; Definition 13 of the legacy theory). -/
def SO.immediatelyContains (x y : SO) : Prop := y.val ∈ Nonplanar.rootChildren x.val

instance (x y : SO) : Decidable (SO.immediatelyContains x y) :=
  inferInstanceAs (Decidable (_ ∈ _))

@[simp] theorem SO.immediatelyContains_lexLeaf (tok : LIToken) (y : SO) :
    ¬ SO.immediatelyContains (SO.lexLeaf tok) y := by
  simp only [SO.immediatelyContains, SO.lexLeaf, Nonplanar.leaf, Nonplanar.rootChildren_mk,
    Planar.leaf, Planar.children, List.map_nil, Multiset.coe_nil, Multiset.notMem_zero,
    not_false_iff]

@[simp] theorem SO.immediatelyContains_traceLeaf (y : SO) :
    ¬ SO.immediatelyContains SO.traceLeaf y := by
  simp only [SO.immediatelyContains, SO.traceLeaf, Nonplanar.leaf, Nonplanar.rootChildren_mk,
    Planar.leaf, Planar.children, List.map_nil, Multiset.coe_nil, Multiset.notMem_zero,
    not_false_iff]

@[simp] theorem SO.immediatelyContains_node (l r y : SO) :
    SO.immediatelyContains (SO.node l r) y ↔ y = l ∨ y = r := by
  rw [SO.immediatelyContains, SO.node_val, Nonplanar.rootChildren_node,
      Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
  exact ⟨fun h => h.imp Subtype.ext Subtype.ext,
         fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val)⟩

/-! ### Subterm enumeration

`Nonplanar.rootChildren` is single-level, so deep enumeration is built fresh at the
planar level and lifted. The result is a multiset of *nonplanar* subtrees; its
`PlanarEquiv`-invariance lets it descend to the quotient. -/

mutual
/-- All subtrees of a planar tree (incl. the root), as nonplanar trees. -/
def subtreesNPlanar : Planar SOLabel → Multiset (Nonplanar SOLabel)
  | .node a cs => Nonplanar.mk (.node a cs) ::ₘ subtreesNPlanarList cs
/-- Auxiliary: union of subtree-multisets across a child list. -/
def subtreesNPlanarList : List (Planar SOLabel) → Multiset (Nonplanar SOLabel)
  | []      => 0
  | c :: cs => subtreesNPlanar c + subtreesNPlanarList cs
end

/-- `subtreesNPlanarList` is a multiset sum, hence permutation-invariant. -/
private theorem subtreesNPlanarList_perm {cs ds : List (Planar SOLabel)}
    (h : cs.Perm ds) : subtreesNPlanarList cs = subtreesNPlanarList ds := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [subtreesNPlanarList]; rw [ih]
  | swap _ _ _ => simp only [subtreesNPlanarList]; rw [add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Replacing one child by a subtree-equal child preserves the list sum. -/
private theorem subtreesNPlanarList_replace (pre post : List (Planar SOLabel))
    {old new : Planar SOLabel} (h : subtreesNPlanar old = subtreesNPlanar new) :
    subtreesNPlanarList (pre ++ old :: post) = subtreesNPlanarList (pre ++ new :: post) := by
  induction pre with
  | nil => simp only [List.nil_append, subtreesNPlanarList]; rw [h]
  | cons hd tl ih => simp only [List.cons_append, subtreesNPlanarList]; rw [ih]

private theorem subtreesNPlanar_planarStep {t s : Planar SOLabel}
    (hstep : Planar.PlanarStep t s) : subtreesNPlanar t = subtreesNPlanar s := by
  induction hstep with
  | @swapAtRoot a l r pre post =>
    simp only [subtreesNPlanar]
    rw [Nonplanar.mk_step Planar.PlanarStep.swapAtRoot,
        subtreesNPlanarList_perm (List.Perm.append_left pre (.swap r l post))]
  | @recurse a pre old new post hstep ih =>
    simp only [subtreesNPlanar]
    rw [Nonplanar.mk_step (Planar.PlanarStep.recurse hstep),
        subtreesNPlanarList_replace pre post ih]

/-- `subtreesNPlanar` is `PlanarEquiv`-invariant, so it descends to `Nonplanar`. -/
theorem subtreesNPlanar_planarEquiv {t s : Planar SOLabel}
    (h : Planar.PlanarEquiv t s) : subtreesNPlanar t = subtreesNPlanar s := by
  induction h with
  | rel _ _ hstep => exact subtreesNPlanar_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- All subtrees of a nonplanar tree (incl. the root). -/
def subtreesN : Nonplanar SOLabel → Multiset (Nonplanar SOLabel) :=
  Nonplanar.lift subtreesNPlanar (fun _ _ h => subtreesNPlanar_planarEquiv h)

@[simp] theorem subtreesN_mk (t : Planar SOLabel) :
    subtreesN (Nonplanar.mk t) = subtreesNPlanar t := rfl

theorem subtreesN_leaf (a : SOLabel) : subtreesN (Nonplanar.leaf a) = {Nonplanar.leaf a} := by
  show subtreesNPlanar (Planar.leaf a) = _
  simp only [Planar.leaf, subtreesNPlanar, subtreesNPlanarList]
  rfl

/-- `subtreesN` on a bare binary node: the node plus the subtrees of each child. -/
theorem subtreesN_node (a b : Nonplanar SOLabel) :
    subtreesN (Nonplanar.node (Sum.inr ()) {a, b})
      = Nonplanar.node (Sum.inr ()) {a, b} ::ₘ (subtreesN a + subtreesN b) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (Planar.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl,
        Nonplanar.node_mk_planar_list]
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
  show Nonplanar.mk (Planar.node lbl cs) ∈ subtreesNPlanar (Planar.node lbl cs)
  rw [subtreesNPlanar]; exact Multiset.mem_cons_self _ _

/-! ### `SO.subtrees` / `SO.Acc` -/

/-- Subtrees of a syntactic object are themselves syntactic objects. -/
theorem subtreesN_closure (s : SO) : ∀ m ∈ subtreesN s.val, IsSO m := by
  induction s using SO.ind with
  | lex tok =>
    intro m hm
    rw [show (SO.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl,
        mem_subtreesN_leaf] at hm
    subst hm; exact (SO.lexLeaf tok).2
  | trace =>
    intro m hm
    rw [show SO.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl, mem_subtreesN_leaf] at hm
    subst hm; exact SO.traceLeaf.2
  | node l r ihl ihr =>
    intro m hm
    rw [SO.node_val, mem_subtreesN_node] at hm
    rcases hm with rfl | hl | hr
    · exact (SO.node l r).2
    · exact ihl m hl
    · exact ihr m hr

/-- All subtrees of a syntactic object (incl. the root), as syntactic objects
    ([marcolli-chomsky-berwick-2025] §1.2; the legacy `SyntacticObject.subtrees`). -/
def SO.subtrees (s : SO) : Multiset SO :=
  (subtreesN s.val).pmap (fun m h => ⟨m, h⟩) (subtreesN_closure s)

@[simp] theorem SO.mem_subtrees {x s : SO} : x ∈ s.subtrees ↔ x.val ∈ subtreesN s.val := by
  rw [SO.subtrees, Multiset.mem_pmap]
  constructor
  · rintro ⟨m, hm, he⟩; rw [← he]; exact hm
  · intro h; exact ⟨x.val, h, Subtype.ext rfl⟩

/-- The root is among its own subtrees. -/
theorem SO.self_mem_subtrees (s : SO) : s ∈ s.subtrees := by
  rw [SO.mem_subtrees]; exact self_mem_subtreesN s.val

/-- Subtree membership at a bare binary node: the node itself, or a subtree of a
    daughter. -/
@[simp] theorem SO.mem_subtrees_node {x l r : SO} :
    x ∈ (SO.node l r).subtrees ↔ x = SO.node l r ∨ x ∈ l.subtrees ∨ x ∈ r.subtrees := by
  rw [SO.mem_subtrees, SO.node_val, mem_subtreesN_node, ← SO.mem_subtrees, ← SO.mem_subtrees]
  exact Iff.or ⟨fun h => Subtype.ext h, fun h => by rw [h, SO.node_val]⟩ Iff.rfl

/-- `subtrees` is downward-closed along the subtree relation: every subtree of a
    subtree of `s` is a subtree of `s`. -/
theorem SO.subtrees_subset_of_mem {w s : SO} (h : w ∈ s.subtrees) :
    w.subtrees ⊆ s.subtrees := by
  induction s using SO.ind with
  | lex tok =>
    rw [SO.mem_subtrees, show (SO.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl,
        mem_subtreesN_leaf] at h
    rw [(Subtype.ext h : w = SO.lexLeaf tok)]; exact Multiset.Subset.refl _
  | trace =>
    rw [SO.mem_subtrees, show SO.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl,
        mem_subtreesN_leaf] at h
    rw [(Subtype.ext h : w = SO.traceLeaf)]; exact Multiset.Subset.refl _
  | node l r ihl ihr =>
    rw [SO.mem_subtrees_node] at h
    rcases h with rfl | hl | hr
    · exact Multiset.Subset.refl _
    · intro z hz; rw [SO.mem_subtrees_node]; exact Or.inr (Or.inl (ihl hl hz))
    · intro z hz; rw [SO.mem_subtrees_node]; exact Or.inr (Or.inr (ihr hr hz))

end Minimalist
