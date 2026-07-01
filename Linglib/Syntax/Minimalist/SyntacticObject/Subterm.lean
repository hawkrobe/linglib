/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

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
    Tree.leaf, Tree.children, List.map_nil, Multiset.coe_nil, Multiset.notMem_zero,
    not_false_iff]

@[simp] theorem SO.immediatelyContains_traceLeaf (y : SO) :
    ¬ SO.immediatelyContains SO.traceLeaf y := by
  simp only [SO.immediatelyContains, SO.traceLeaf, Nonplanar.leaf, Nonplanar.rootChildren_mk,
    Tree.leaf, Tree.children, List.map_nil, Multiset.coe_nil, Multiset.notMem_zero,
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
`PermEquiv`-invariance lets it descend to the quotient. -/

mutual
/-- All subtrees of a planar tree (incl. the root), as nonplanar trees. -/
def subtreesNPlanar : Tree SOLabel → Multiset (Nonplanar SOLabel)
  | .node a cs => Nonplanar.mk (.node a cs) ::ₘ subtreesNPlanarList cs
/-- Auxiliary: union of subtree-multisets across a child list. -/
def subtreesNPlanarList : List (Tree SOLabel) → Multiset (Nonplanar SOLabel)
  | []      => 0
  | c :: cs => subtreesNPlanar c + subtreesNPlanarList cs
end

/-- `subtreesNPlanarList` is a multiset sum, hence permutation-invariant. -/
private theorem subtreesNPlanarList_perm {cs ds : List (Tree SOLabel)}
    (h : cs.Perm ds) : subtreesNPlanarList cs = subtreesNPlanarList ds := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [subtreesNPlanarList]; rw [ih]
  | swap _ _ _ => simp only [subtreesNPlanarList]; rw [add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Replacing one child by a subtree-equal child preserves the list sum. -/
private theorem subtreesNPlanarList_replace (pre post : List (Tree SOLabel))
    {old new : Tree SOLabel} (h : subtreesNPlanar old = subtreesNPlanar new) :
    subtreesNPlanarList (pre ++ old :: post) = subtreesNPlanarList (pre ++ new :: post) := by
  induction pre with
  | nil => simp only [List.nil_append, subtreesNPlanarList]; rw [h]
  | cons hd tl ih => simp only [List.cons_append, subtreesNPlanarList]; rw [ih]

private theorem subtreesNPlanar_permStep {t s : Tree SOLabel}
    (hstep : Tree.PermStep t s) : subtreesNPlanar t = subtreesNPlanar s := by
  induction hstep with
  | @swapAtRoot a l r pre post =>
    simp only [subtreesNPlanar]
    rw [Nonplanar.mk_step Tree.PermStep.swapAtRoot,
        subtreesNPlanarList_perm (List.Perm.append_left pre (.swap r l post))]
  | @recurse a pre old new post hstep ih =>
    simp only [subtreesNPlanar]
    rw [Nonplanar.mk_step (Tree.PermStep.recurse hstep),
        subtreesNPlanarList_replace pre post ih]

/-- `subtreesNPlanar` is `PermEquiv`-invariant, so it descends to `Nonplanar`. -/
theorem subtreesNPlanar_permEquiv {t s : Tree SOLabel}
    (h : Tree.PermEquiv t s) : subtreesNPlanar t = subtreesNPlanar s := by
  induction h with
  | rel _ _ hstep => exact subtreesNPlanar_permStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- All subtrees of a nonplanar tree (incl. the root). -/
def subtreesN : Nonplanar SOLabel → Multiset (Nonplanar SOLabel) :=
  Nonplanar.lift subtreesNPlanar (fun _ _ h => subtreesNPlanar_permEquiv h)

@[simp] theorem subtreesN_mk (t : Tree SOLabel) :
    subtreesN (Nonplanar.mk t) = subtreesNPlanar t := rfl

theorem subtreesN_leaf (a : SOLabel) : subtreesN (Nonplanar.leaf a) = {Nonplanar.leaf a} := by
  show subtreesNPlanar (Tree.leaf a) = _
  simp only [Tree.leaf, subtreesNPlanar, subtreesNPlanarList]
  rfl

/-- `subtreesN` on a bare binary node: the node plus the subtrees of each child. -/
theorem subtreesN_node (a b : Nonplanar SOLabel) :
    subtreesN (Nonplanar.node (Sum.inr ()) {a, b})
      = Nonplanar.node (Sum.inr ()) {a, b} ::ₘ (subtreesN a + subtreesN b) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (Tree.node (Sum.inr ()) [pa, pb]) := by
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
  show Nonplanar.mk (Tree.node lbl cs) ∈ subtreesNPlanar (Tree.node lbl cs)
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

/-! ### Cardinality (MCB's vertex/accessible-term counts, Def 1.2.2 eq. 1.2.5) -/

mutual
/-- `subtreesN` has one element per vertex: its cardinality is the node count. -/
theorem subtreesNPlanar_card (p : Tree SOLabel) :
    (subtreesNPlanar p).card = p.numNodes := by
  obtain ⟨a, cs⟩ := p
  rw [subtreesNPlanar, Multiset.card_cons, subtreesNPlanarList_card, Tree.numNodes_node]; omega
/-- Auxiliary list version. -/
theorem subtreesNPlanarList_card (cs : List (Tree SOLabel)) :
    (subtreesNPlanarList cs).card = (cs.map Tree.numNodes).sum := by
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
theorem SO.subtrees_card (s : SO) : (s.subtrees).card = Nonplanar.numNodes s.val := by
  rw [SO.subtrees, Multiset.card_pmap, subtreesN_card]

/-! ### Accessible terms `Acc(T)` (Def 1.2.2) -/

/-- MCB's accessible-terms operator `Acc(T)` ([marcolli-chomsky-berwick-2025]
    Def 1.2.2, eq. 1.2.2): the subtrees at **all non-root vertices** (leaves
    included — the counting identity eq. 1.2.5 `#V = b₀ + #Acc` forces this).
    Defined as `subtrees − {self}` (`Acc'(T) = {T} ∪ Acc(T)`, eq. 1.2.3). -/
def SO.Acc (s : SO) : Multiset SO := s.subtrees - {s}

/-- **MCB counting identity** (eq. 1.2.5, one-component case): `#Acc(T) = #V(T) − 1`. -/
theorem SO.Acc_card (s : SO) : (s.Acc).card = Nonplanar.numNodes s.val - 1 := by
  rw [SO.Acc, Multiset.card_sub (Multiset.singleton_le.mpr (SO.self_mem_subtrees s)),
      SO.subtrees_card, Multiset.card_singleton]

@[simp] theorem SO.Acc_lexLeaf (tok : LIToken) : (SO.lexLeaf tok).Acc = 0 := by
  rw [← Multiset.card_eq_zero, SO.Acc_card,
      show (SO.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl, Nonplanar.numNodes_leaf]

@[simp] theorem SO.Acc_traceLeaf : SO.traceLeaf.Acc = 0 := by
  rw [← Multiset.card_eq_zero, SO.Acc_card,
      show SO.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl, Nonplanar.numNodes_leaf]

/-! ### Containment / dominance -/

/-- Weight of a bare binary node is one more than the sum of its daughters'. -/
theorem weight_node_pair (a b : Nonplanar SOLabel) :
    Nonplanar.numNodes (Nonplanar.node (Sum.inr ()) {a, b})
      = Nonplanar.numNodes a + Nonplanar.numNodes b + 1 := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (Tree.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]
  show Nonplanar.numNodes (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = Nonplanar.numNodes (Nonplanar.mk pa) + Nonplanar.numNodes (Nonplanar.mk pb) + 1
  rw [key]
  show (Tree.node (Sum.inr ()) [pa, pb]).numNodes = pa.numNodes + pb.numNodes + 1
  simp only [Tree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega

/-- **Containment (dominance)** is the transitive closure of immediate containment
    ([marcolli-chomsky-berwick-2025] §1.1; the legacy `contains`). -/
inductive SO.contains : SO → SO → Prop
  | imm : ∀ x y, SO.immediatelyContains x y → SO.contains x y
  | trans : ∀ x y z, SO.immediatelyContains x z → SO.contains z y → SO.contains x y

theorem SO.imm_implies_contains {x y : SO} (h : SO.immediatelyContains x y) :
    SO.contains x y := .imm x y h

theorem SO.contains_trans {x y z : SO} (hxy : SO.contains x y) (hyz : SO.contains y z) :
    SO.contains x z := by
  induction hxy with
  | imm x y himm => exact .trans x z y himm hyz
  | trans x y w himm _ ih => exact .trans x z w himm (ih hyz)

/-- Immediate containment strictly decreases weight. -/
theorem SO.immediatelyContains_lt_weight {x y : SO} (h : SO.immediatelyContains x y) :
    Nonplanar.numNodes y.val < Nonplanar.numNodes x.val := by
  rcases SO.exists_form x with ⟨tok, rfl⟩ | rfl | ⟨l, r, rfl⟩
  · exact absurd h (SO.immediatelyContains_lexLeaf tok y)
  · exact absurd h (SO.immediatelyContains_traceLeaf y)
  · rw [SO.immediatelyContains_node] at h
    rw [SO.node_val, weight_node_pair]
    rcases h with rfl | rfl <;> omega

/-- Containment strictly decreases weight; hence it is irreflexive. -/
theorem SO.contains_lt_weight {x y : SO} (h : SO.contains x y) :
    Nonplanar.numNodes y.val < Nonplanar.numNodes x.val := by
  induction h with
  | imm _ _ himm => exact SO.immediatelyContains_lt_weight himm
  | trans _ _ _ himm _ ih => exact lt_trans ih (SO.immediatelyContains_lt_weight himm)

theorem SO.contains_irrefl (x : SO) : ¬ SO.contains x x :=
  fun h => absurd (SO.contains_lt_weight h) (lt_irrefl _)

/-! ### Subtree ↔ containment bridge -/

theorem SO.mem_subtrees_of_immediatelyContains {x y : SO} (h : SO.immediatelyContains x y) :
    y ∈ x.subtrees := by
  rcases SO.exists_form x with ⟨tok, rfl⟩ | rfl | ⟨l, r, rfl⟩
  · exact absurd h (SO.immediatelyContains_lexLeaf tok y)
  · exact absurd h (SO.immediatelyContains_traceLeaf y)
  · rw [SO.immediatelyContains_node] at h
    rcases h with heq | heq
    · rw [heq, SO.mem_subtrees_node]; exact Or.inr (Or.inl (SO.self_mem_subtrees l))
    · rw [heq, SO.mem_subtrees_node]; exact Or.inr (Or.inr (SO.self_mem_subtrees r))

theorem SO.mem_subtrees_of_contains {x y : SO} (h : SO.contains x y) : y ∈ x.subtrees := by
  induction h with
  | imm x y himm => exact SO.mem_subtrees_of_immediatelyContains himm
  | trans x y w himm _ ih =>
    exact SO.subtrees_subset_of_mem (SO.mem_subtrees_of_immediatelyContains himm) ih

/-- A subtree of `x` is either `x` itself or properly contained in `x`. -/
theorem SO.mem_subtrees_iff_eq_or_contains {x y : SO} :
    y ∈ x.subtrees ↔ y = x ∨ SO.contains x y := by
  refine ⟨fun h => ?_, fun h => h.elim (fun he => he ▸ SO.self_mem_subtrees x)
    SO.mem_subtrees_of_contains⟩
  induction x using SO.ind with
  | lex tok =>
    rw [SO.mem_subtrees, show (SO.lexLeaf tok).val = Nonplanar.leaf (Sum.inl tok) from rfl,
        mem_subtreesN_leaf] at h
    exact Or.inl (Subtype.ext h)
  | trace =>
    rw [SO.mem_subtrees, show SO.traceLeaf.val = Nonplanar.leaf (Sum.inr ()) from rfl,
        mem_subtreesN_leaf] at h
    exact Or.inl (Subtype.ext h)
  | node l r ihl ihr =>
    rw [SO.mem_subtrees_node] at h
    rcases h with rfl | hl | hr
    · exact Or.inl rfl
    · refine Or.inr ?_
      rcases ihl hl with heq | hc
      · rw [heq]; exact .imm _ _ ((SO.immediatelyContains_node l r l).mpr (Or.inl rfl))
      · exact .trans _ _ l ((SO.immediatelyContains_node l r l).mpr (Or.inl rfl)) hc
    · refine Or.inr ?_
      rcases ihr hr with heq | hc
      · rw [heq]; exact .imm _ _ ((SO.immediatelyContains_node l r r).mpr (Or.inr rfl))
      · exact .trans _ _ r ((SO.immediatelyContains_node l r r).mpr (Or.inr rfl)) hc

/-- **Containment ↔ proper subtree membership.** Gives a decision procedure for
    `contains` without well-founded recursion: `y` is properly contained in `x` iff
    it is a subtree distinct from `x`. -/
theorem SO.contains_iff_mem_subtrees_and_ne {x y : SO} :
    SO.contains x y ↔ y ∈ x.subtrees ∧ y ≠ x := by
  constructor
  · intro h
    exact ⟨SO.mem_subtrees_of_contains h, fun he => SO.contains_irrefl x (he ▸ h)⟩
  · rintro ⟨hmem, hne⟩
    rcases SO.mem_subtrees_iff_eq_or_contains.mp hmem with rfl | hc
    · exact absurd rfl hne
    · exact hc

instance (x y : SO) : Decidable (SO.contains x y) :=
  decidable_of_iff _ SO.contains_iff_mem_subtrees_and_ne.symm

/-! ### Term-of and reflexive containment -/

/-- `x` is a **term of** `y`: `x = y` or `y` contains `x`. -/
def SO.isTermOf (x y : SO) : Prop := x = y ∨ SO.contains y x

instance (x y : SO) : Decidable (SO.isTermOf x y) := inferInstanceAs (Decidable (_ ∨ _))

theorem SO.isTermOf_iff_mem_subtrees (x y : SO) : SO.isTermOf x y ↔ x ∈ y.subtrees :=
  SO.mem_subtrees_iff_eq_or_contains.symm

/-- Reflexive containment. -/
def SO.containsOrEq (x y : SO) : Prop := x = y ∨ SO.contains x y

instance (x y : SO) : Decidable (SO.containsOrEq x y) := inferInstanceAs (Decidable (_ ∨ _))

theorem SO.containsOrEq_trans {x y z : SO}
    (hxy : SO.containsOrEq x y) (hyz : SO.containsOrEq y z) : SO.containsOrEq x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  · rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (SO.contains_trans hxy hyz)

/-! ### Tree-relative c-command ([reinhart-1976]) -/

/-- `x` and `y` are **sisters in** `root`: distinct co-daughters of some subtree. -/
def SO.areSistersIn (root x y : SO) : Prop :=
  ∃ z ∈ root.subtrees, SO.immediatelyContains z x ∧ SO.immediatelyContains z y ∧ x ≠ y

instance (root x y : SO) : Decidable (SO.areSistersIn root x y) :=
  Multiset.decidableExistsMultiset

/-- `x` **c-commands** `y` in `root`: `x` has a sister (in `root`) that
    contains-or-equals `y`. -/
def SO.cCommandsIn (root x y : SO) : Prop :=
  ∃ z ∈ root.subtrees, SO.areSistersIn root x z ∧ SO.containsOrEq z y

instance (root x y : SO) : Decidable (SO.cCommandsIn root x y) :=
  Multiset.decidableExistsMultiset

/-- `x` **asymmetrically** c-commands `y` in `root`. -/
def SO.asymCCommandsIn (root x y : SO) : Prop :=
  SO.cCommandsIn root x y ∧ ¬ SO.cCommandsIn root y x

instance (root x y : SO) : Decidable (SO.asymCCommandsIn root x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### `decide` demonstrations

The containment / c-command decision procedures reduce on concrete trees built
via `Nonplanar.mk ∘ Tree.node` (not the noncomputable `SO.node`), confirming the
"state result trees directly" discipline carries through to the relational layer. -/

private def demoL : SO := ⟨Nonplanar.mk (.node (Sum.inl (mkTraceToken 0)) []), by decide⟩
private def demoR : SO := ⟨Nonplanar.mk (.node (Sum.inl (mkTraceToken 1)) []), by decide⟩
private def demoT : SO :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl (mkTraceToken 0)) [], .node (Sum.inl (mkTraceToken 1)) []]), by decide⟩

/-- The root properly contains its left daughter; the daughter does not contain the root. -/
example : SO.contains demoT demoL ∧ ¬ SO.contains demoL demoT := by decide
/-- The two daughters c-command each other in the root. -/
example : SO.cCommandsIn demoT demoL demoR := by decide
/-- A node has one more vertex than the sum of its daughters' (eq. 1.2.5 witness). -/
example : (demoT.subtrees).card = 3 := by decide

end Minimalist
