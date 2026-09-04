/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Count
import Linglib.Core.Data.RoseTree.Subtree
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Subterms, containment, and c-command

The subterm theory of syntactic objects. `subtrees` enumerates the subterms, root included, as
syntactic objects, and its cardinality is the vertex count; the accessible terms `Acc` are the
subterms at non-root vertices, so `#Acc = #V − 1`. Containment is the transitive closure of
immediate containment, strictly decreases the vertex count, and coincides with proper subterm
membership, which makes it decidable. Sisterhood and c-command are relative to a root.

## Main definitions

* `Minimalist.SyntacticObject.immediatelyContains`, `contains`, `isTermOf`, `containsOrEq`
* `Minimalist.SyntacticObject.subtrees`, `Acc`
* `Minimalist.SyntacticObject.areSistersIn`, `cCommandsIn`, `asymCCommandsIn`,
  `immediatelyCCommandsIn`

## Main results

* `Minimalist.SyntacticObject.contains_iff_mem_subtrees_and_ne`: containment is proper subterm
  membership.
* `Minimalist.SyntacticObject.Acc_card`: the accessible terms number one less than the vertices.

## References

* [marcolli-chomsky-berwick-2025], §1.2 (Definition 1.2.2)
* [reinhart-1976]
-/

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

namespace SyntacticObject

/-! ### Immediate containment -/

/-- `y` is one of `x`'s root daughters. -/
def immediatelyContains (x y : SyntacticObject) : Prop :=
  y.val ∈ UnorderedTree.rootChildren x.val

instance (x y : SyntacticObject) : Decidable (immediatelyContains x y) :=
  inferInstanceAs (Decidable (_ ∈ _))

@[simp] theorem immediatelyContains_leaf (tok : LIToken) (y : SyntacticObject) :
    ¬ immediatelyContains (SyntacticObject.leaf tok) y := by
  simp only [immediatelyContains, leaf, UnorderedTree.leaf,
    UnorderedTree.rootChildren_mk, RoseTree.leaf, RoseTree.children, List.map_nil, Multiset.coe_nil,
    Multiset.notMem_zero, not_false_iff]

@[simp] theorem immediatelyContains_trace (y : SyntacticObject) :
    ¬ immediatelyContains trace y := by
  simp only [immediatelyContains, trace, UnorderedTree.leaf,
    UnorderedTree.rootChildren_mk, RoseTree.leaf, RoseTree.children, List.map_nil, Multiset.coe_nil,
    Multiset.notMem_zero, not_false_iff]

@[simp] theorem immediatelyContains_traceOf (tok : LIToken) (y : SyntacticObject) :
    ¬ immediatelyContains (traceOf tok) y := by
  simp only [immediatelyContains, traceOf, UnorderedTree.leaf,
    UnorderedTree.rootChildren_mk, RoseTree.leaf, RoseTree.children, List.map_nil, Multiset.coe_nil,
    Multiset.notMem_zero, not_false_iff]

@[simp] theorem immediatelyContains_merge (l r y : SyntacticObject) :
    immediatelyContains (merge l r) y ↔ y = l ∨ y = r := by
  rw [immediatelyContains, merge_val, UnorderedTree.rootChildren_node,
      Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
  exact ⟨fun h => h.imp Subtype.ext Subtype.ext,
         fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val)⟩

end SyntacticObject

/-! ### Subterms -/

/-- The subtrees of a syntactic object are syntactic objects. -/
theorem isSyntacticObject_of_mem_subtrees (s : SyntacticObject) :
    ∀ m ∈ UnorderedTree.subtrees s.val,
    IsSyntacticObject m := by
  induction s using ind with
  | leaf tok =>
    intro m hm
    rw [show (SyntacticObject.leaf tok).val = UnorderedTree.leaf (Sum.inl tok) from rfl,
        UnorderedTree.mem_subtrees_leaf] at hm
    subst hm; exact (SyntacticObject.leaf tok).2
  | trace =>
    intro m hm
    rw [show trace.val = UnorderedTree.leaf (Sum.inr none) from rfl,
        UnorderedTree.mem_subtrees_leaf] at hm
    subst hm; exact trace.2
  | traceOf tok =>
    intro m hm
    rw [show (traceOf tok).val = UnorderedTree.leaf (Sum.inr (some tok)) from rfl,
        UnorderedTree.mem_subtrees_leaf] at hm
    subst hm; exact (traceOf tok).2
  | merge l r ihl ihr =>
    intro m hm
    rw [merge_val, UnorderedTree.mem_subtrees_node_pair] at hm
    rcases hm with rfl | hl | hr
    · exact (merge l r).2
    · exact ihl m hl
    · exact ihr m hr

namespace SyntacticObject

/-- All subterms of a syntactic object, the root included. -/
def subtrees (s : SyntacticObject) : Multiset SyntacticObject :=
  (UnorderedTree.subtrees s.val).pmap (fun m h => ⟨m, h⟩) (isSyntacticObject_of_mem_subtrees s)

@[simp] theorem mem_subtrees {x s : SyntacticObject} :
    x ∈ s.subtrees ↔ x.val ∈ UnorderedTree.subtrees s.val := by
  rw [subtrees, Multiset.mem_pmap]
  constructor
  · rintro ⟨m, hm, he⟩; rw [← he]; exact hm
  · intro h; exact ⟨x.val, h, Subtype.ext rfl⟩

theorem self_mem_subtrees (s : SyntacticObject) : s ∈ s.subtrees := by
  rw [mem_subtrees]; exact UnorderedTree.self_mem_subtrees s.val

@[simp] theorem mem_subtrees_merge {x l r : SyntacticObject} :
    x ∈ (merge l r).subtrees ↔ x = merge l r ∨ x ∈ l.subtrees ∨ x ∈ r.subtrees := by
  rw [mem_subtrees, merge_val, UnorderedTree.mem_subtrees_node_pair, ← mem_subtrees, ← mem_subtrees]
  exact Iff.or ⟨fun h => Subtype.ext h, fun h => by rw [h, merge_val]⟩ Iff.rfl

/-- A subterm of a subterm of `s` is a subterm of `s`. -/
theorem subtrees_subset_of_mem {w s : SyntacticObject} (h : w ∈ s.subtrees) :
    w.subtrees ⊆ s.subtrees := by
  induction s using ind with
  | leaf tok =>
    rw [mem_subtrees, show (SyntacticObject.leaf tok).val = UnorderedTree.leaf
      (Sum.inl tok) from rfl,
        UnorderedTree.mem_subtrees_leaf] at h
    rw [(Subtype.ext h : w = SyntacticObject.leaf tok)]; exact Multiset.Subset.refl _
  | trace =>
    rw [mem_subtrees, show trace.val = UnorderedTree.leaf (Sum.inr none) from rfl,
        UnorderedTree.mem_subtrees_leaf] at h
    rw [(Subtype.ext h : w = trace)]; exact Multiset.Subset.refl _
  | traceOf tok =>
    rw [mem_subtrees, show (traceOf tok).val = UnorderedTree.leaf (Sum.inr (some tok)) from rfl,
        UnorderedTree.mem_subtrees_leaf] at h
    rw [(Subtype.ext h : w = traceOf tok)]; exact Multiset.Subset.refl _
  | merge l r ihl ihr =>
    rw [mem_subtrees_merge] at h
    rcases h with rfl | hl | hr
    · exact Multiset.Subset.refl _
    · intro z hz; rw [mem_subtrees_merge]; exact Or.inr (Or.inl (ihl hl hz))
    · intro z hz; rw [mem_subtrees_merge]; exact Or.inr (Or.inr (ihr hr hz))

/-- One subterm per vertex. -/
theorem subtrees_card (s : SyntacticObject) : (s.subtrees).card = UnorderedTree.numNodes s.val := by
  rw [subtrees, Multiset.card_pmap, UnorderedTree.card_subtrees]

/-! ### Accessible terms -/

/-- The accessible terms: the subterms at non-root vertices, `subtrees − {s}`. -/
def Acc (s : SyntacticObject) : Multiset SyntacticObject := s.subtrees - {s}

/-- `#Acc s = #V s − 1`. -/
theorem Acc_card (s : SyntacticObject) : (s.Acc).card = UnorderedTree.numNodes s.val - 1 := by
  rw [Acc, Multiset.card_sub (Multiset.singleton_le.mpr (self_mem_subtrees s)),
      subtrees_card, Multiset.card_singleton]

@[simp] theorem Acc_leaf (tok : LIToken) : (SyntacticObject.leaf tok).Acc = 0 := by
  rw [← Multiset.card_eq_zero, Acc_card,
      show (SyntacticObject.leaf tok).val = UnorderedTree.leaf (Sum.inl tok) from rfl,
      UnorderedTree.numNodes_leaf]

@[simp] theorem Acc_trace : trace.Acc = 0 := by
  rw [← Multiset.card_eq_zero, Acc_card,
      show trace.val = UnorderedTree.leaf (Sum.inr none) from rfl,
      UnorderedTree.numNodes_leaf]

/-! ### Containment -/

/-- Containment: the transitive closure of immediate containment. -/
inductive contains : SyntacticObject → SyntacticObject → Prop
  | imm : ∀ x y, immediatelyContains x y → contains x y
  | trans : ∀ x y z, immediatelyContains x z → contains z y → contains x y

theorem imm_implies_contains {x y : SyntacticObject} (h : immediatelyContains x y) :
    contains x y := .imm x y h

theorem contains_trans {x y z : SyntacticObject} (hxy : contains x y) (hyz : contains y z) :
    contains x z := by
  induction hxy with
  | imm x y himm => exact .trans x z y himm hyz
  | trans x y w himm _ ih => exact .trans x z w himm (ih hyz)

theorem immediatelyContains_lt_weight {x y : SyntacticObject} (h : immediatelyContains x y) :
    UnorderedTree.numNodes y.val < UnorderedTree.numNodes x.val := by
  rcases exists_form x with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩
  · exact absurd h (immediatelyContains_leaf tok y)
  · exact absurd h (immediatelyContains_trace y)
  · exact absurd h (immediatelyContains_traceOf tok y)
  · rw [immediatelyContains_merge] at h
    rw [merge_val, UnorderedTree.numNodes_node_pair]
    rcases h with rfl | rfl <;> omega

theorem contains_lt_weight {x y : SyntacticObject} (h : contains x y) :
    UnorderedTree.numNodes y.val < UnorderedTree.numNodes x.val := by
  induction h with
  | imm _ _ himm => exact immediatelyContains_lt_weight himm
  | trans _ _ _ himm _ ih => exact lt_trans ih (immediatelyContains_lt_weight himm)

theorem contains_irrefl (x : SyntacticObject) : ¬ contains x x :=
  fun h => absurd (contains_lt_weight h) (lt_irrefl _)

theorem mem_subtrees_of_immediatelyContains {x y : SyntacticObject}
    (h : immediatelyContains x y) : y ∈ x.subtrees := by
  rcases exists_form x with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩
  · exact absurd h (immediatelyContains_leaf tok y)
  · exact absurd h (immediatelyContains_trace y)
  · exact absurd h (immediatelyContains_traceOf tok y)
  · rw [immediatelyContains_merge] at h
    rcases h with heq | heq
    · rw [heq, mem_subtrees_merge]
      exact Or.inr (Or.inl (self_mem_subtrees l))
    · rw [heq, mem_subtrees_merge]
      exact Or.inr (Or.inr (self_mem_subtrees r))

theorem mem_subtrees_of_contains {x y : SyntacticObject} (h : contains x y) :
    y ∈ x.subtrees := by
  induction h with
  | imm x y himm => exact mem_subtrees_of_immediatelyContains himm
  | trans x y w himm _ ih =>
    exact subtrees_subset_of_mem (mem_subtrees_of_immediatelyContains himm) ih

theorem mem_subtrees_iff_eq_or_contains {x y : SyntacticObject} :
    y ∈ x.subtrees ↔ y = x ∨ contains x y := by
  refine ⟨fun h => ?_, fun h => h.elim (fun he => he ▸ self_mem_subtrees x)
    mem_subtrees_of_contains⟩
  induction x using ind with
  | leaf tok =>
    rw [mem_subtrees, show (SyntacticObject.leaf tok).val = UnorderedTree.leaf
      (Sum.inl tok) from rfl,
        UnorderedTree.mem_subtrees_leaf] at h
    exact Or.inl (Subtype.ext h)
  | trace =>
    rw [mem_subtrees, show trace.val = UnorderedTree.leaf (Sum.inr none) from rfl,
        UnorderedTree.mem_subtrees_leaf] at h
    exact Or.inl (Subtype.ext h)
  | traceOf tok =>
    rw [mem_subtrees, show (traceOf tok).val = UnorderedTree.leaf (Sum.inr (some tok)) from rfl,
        UnorderedTree.mem_subtrees_leaf] at h
    exact Or.inl (Subtype.ext h)
  | merge l r ihl ihr =>
    rw [mem_subtrees_merge] at h
    rcases h with rfl | hl | hr
    · exact Or.inl rfl
    · refine Or.inr ?_
      rcases ihl hl with heq | hc
      · rw [heq]; exact .imm _ _ ((immediatelyContains_merge l r l).mpr (Or.inl rfl))
      · exact .trans _ _ l ((immediatelyContains_merge l r l).mpr (Or.inl rfl)) hc
    · refine Or.inr ?_
      rcases ihr hr with heq | hc
      · rw [heq]; exact .imm _ _ ((immediatelyContains_merge l r r).mpr (Or.inr rfl))
      · exact .trans _ _ r ((immediatelyContains_merge l r r).mpr (Or.inr rfl)) hc

/-- Containment is proper subterm membership, which decides it. -/
theorem contains_iff_mem_subtrees_and_ne {x y : SyntacticObject} :
    contains x y ↔ y ∈ x.subtrees ∧ y ≠ x := by
  constructor
  · intro h
    exact ⟨mem_subtrees_of_contains h, fun he => contains_irrefl x (he ▸ h)⟩
  · rintro ⟨hmem, hne⟩
    rcases mem_subtrees_iff_eq_or_contains.mp hmem with rfl | hc
    · exact absurd rfl hne
    · exact hc

instance (x y : SyntacticObject) : Decidable (contains x y) :=
  decidable_of_iff _ contains_iff_mem_subtrees_and_ne.symm

/-- `x` is a term of `y`: `x = y` or `y` contains `x`. -/
def isTermOf (x y : SyntacticObject) : Prop := x = y ∨ contains y x

instance (x y : SyntacticObject) : Decidable (isTermOf x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem isTermOf_iff_mem_subtrees (x y : SyntacticObject) : isTermOf x y ↔ x ∈ y.subtrees :=
  mem_subtrees_iff_eq_or_contains.symm

/-- Reflexive containment. -/
def containsOrEq (x y : SyntacticObject) : Prop := x = y ∨ contains x y

instance (x y : SyntacticObject) : Decidable (containsOrEq x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem containsOrEq_trans {x y z : SyntacticObject}
    (hxy : containsOrEq x y) (hyz : containsOrEq y z) : containsOrEq x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  · rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (contains_trans hxy hyz)

/-! ### C-command -/

/-- `x` and `y` are sisters in `root`: distinct daughters of some subterm of `root`. -/
def areSistersIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.subtrees, immediatelyContains z x ∧ immediatelyContains z y ∧ x ≠ y

instance (root x y : SyntacticObject) : Decidable (areSistersIn root x y) :=
  Multiset.decidableExistsMultiset

/-- `x` c-commands `y` in `root`: a sister of `x` contains or equals `y`. -/
def cCommandsIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.subtrees, areSistersIn root x z ∧ containsOrEq z y

instance (root x y : SyntacticObject) : Decidable (cCommandsIn root x y) :=
  Multiset.decidableExistsMultiset

/-- `x` c-commands `y` in `root` and `y` does not c-command `x`. -/
def asymCCommandsIn (root x y : SyntacticObject) : Prop :=
  cCommandsIn root x y ∧ ¬ cCommandsIn root y x

instance (root x y : SyntacticObject) : Decidable (asymCCommandsIn root x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `x` immediately c-commands `y` in `root`: `x` c-commands `y` with no third object c-commanded
    by `x` and c-commanding `y`. -/
def immediatelyCCommandsIn (root x y : SyntacticObject) : Prop :=
  cCommandsIn root x y ∧ ¬ ∃ z, z ≠ x ∧ z ≠ y ∧ cCommandsIn root x z ∧ cCommandsIn root z y

end SyntacticObject

/-! ### Carrier tests -/

private def demoL : SyntacticObject :=
  ⟨UnorderedTree.mk (.node (Sum.inl (mkTraceToken 0)) []), by decide⟩
private def demoR : SyntacticObject :=
  ⟨UnorderedTree.mk (.node (Sum.inl (mkTraceToken 1)) []), by decide⟩
private def demoT : SyntacticObject :=
  ⟨UnorderedTree.mk (.node (Sum.inr none)
    [.node (Sum.inl (mkTraceToken 0)) [], .node (Sum.inl (mkTraceToken 1)) []]), by decide⟩

/-- The root contains its left daughter and not conversely. -/
example : contains demoT demoL ∧ ¬ contains demoL demoT := by decide
/-- The two daughters c-command each other. -/
example : cCommandsIn demoT demoL demoR := by decide
/-- A node has one more vertex than the sum of its daughters'. -/
example : (demoT.subtrees).card = 3 := by decide

end Minimalist
