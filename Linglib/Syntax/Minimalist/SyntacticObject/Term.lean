/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Relation
import Linglib.Core.Data.RoseTree.Count
import Linglib.Core.Data.RoseTree.Subtree
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Terms, containment, and c-command

This file develops the theory of terms of syntactic objects: containment as a closure of the
daughter relation, the multisets of terms and accessible terms that enumerate it, and
sisterhood and c-command relative to a root. Containment lowers the vertex count, which makes it
a well-founded strict order and decides it.

## Main definitions

* `SyntacticObject.immediatelyContains`: `x` immediately contains `y` when `y` is a
  root daughter of `x`.
* `SyntacticObject.contains`: the transitive closure of immediate containment.
* `SyntacticObject.containsOrEq`: the reflexive transitive closure of immediate
  containment.
* `SyntacticObject.terms`: the terms of an object, itself included, one per vertex.
* `SyntacticObject.accessibleTerms`: the terms at the non-root vertices, the
  accessible terms of [marcolli-chomsky-berwick-2025].
* `SyntacticObject.areSistersIn`: `x` and `y` are sisters in `root` when they are
  distinct daughters of one term of `root`.
* `SyntacticObject.cCommandsIn`: `x` c-commands `y` in `root` when a sister of `x`
  reflexively contains `y` ([reinhart-1976]).
* `SyntacticObject.asymCCommandsIn`: c-command in one direction only.
* `SyntacticObject.domainIn`: the c-command domain of `x` in `root`, the terms it
  c-commands.

## Main results

* `SyntacticObject.mem_terms`, `mem_accessibleTerms`: the terms of `x` are the
  objects it reflexively contains, and the accessible terms those it strictly contains.
* `SyntacticObject.wellFounded_flip_contains`: the proper term relation is
  well-founded.
* `SyntacticObject.card_accessibleTerms`: one accessible term per edge.

## Implementation notes

Syntactic objects are values, not occurrences: a term sitting at two vertices is one object of
multiplicity two in `terms`, and containment and c-command relate values, so the two
daughters of `merge x x` are not sisters.

## References

* [marcolli-chomsky-berwick-2025], Definition 1.2.2
* [reinhart-1976]
-/

namespace Minimalist

open Relation UnorderedTree

namespace SyntacticObject

variable {x y z l r : SyntacticObject}

/-! ### Immediate containment -/

/-- `y` is one of `x`'s root daughters. -/
def immediatelyContains (x y : SyntacticObject) : Prop := y.val ∈ rootChildren x.val

instance (x y : SyntacticObject) : Decidable (immediatelyContains x y) :=
  inferInstanceAs (Decidable (_ ∈ _))

@[simp] theorem immediatelyContains_leaf (tok : LIToken) (y : SyntacticObject) :
    ¬ immediatelyContains (leaf tok) y := by
  simp [immediatelyContains]

@[simp] theorem immediatelyContains_trace (y : SyntacticObject) :
    ¬ immediatelyContains trace y := by
  simp [immediatelyContains]

@[simp] theorem immediatelyContains_traceOf (tok : LIToken) (y : SyntacticObject) :
    ¬ immediatelyContains (traceOf tok) y := by
  simp [immediatelyContains]

@[simp] theorem immediatelyContains_merge (l r y : SyntacticObject) :
    immediatelyContains (merge l r) y ↔ y = l ∨ y = r := by
  simp only [immediatelyContains, merge_val, rootChildren_node, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton]
  exact or_congr Subtype.val_inj Subtype.val_inj

/-! ### Containment -/

/-- Containment, the transitive closure of immediate containment. -/
def contains : SyntacticObject → SyntacticObject → Prop := TransGen immediatelyContains

/-- Reflexive containment, the reflexive transitive closure of immediate containment. -/
def containsOrEq : SyntacticObject → SyntacticObject → Prop := ReflTransGen immediatelyContains

theorem contains_of_immediatelyContains (h : immediatelyContains x y) : contains x y :=
  TransGen.single h

theorem contains_trans (hxy : contains x y) (hyz : contains y z) : contains x z :=
  TransGen.trans hxy hyz

instance : IsPreorder SyntacticObject containsOrEq :=
  inferInstanceAs (IsPreorder _ (ReflTransGen _))

theorem containsOrEq_iff_eq_or_contains : containsOrEq x y ↔ y = x ∨ contains x y :=
  reflTransGen_iff_eq_or_transGen

theorem contains_iff_exists_immediatelyContains :
    contains x y ↔ ∃ z, immediatelyContains x z ∧ containsOrEq z y :=
  TransGen.head'_iff

@[simp] theorem contains_leaf (tok : LIToken) (y : SyntacticObject) :
    ¬ contains (leaf tok) y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_trace (y : SyntacticObject) : ¬ contains trace y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_traceOf (tok : LIToken) (y : SyntacticObject) :
    ¬ contains (traceOf tok) y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_merge :
    contains (merge l r) y ↔ containsOrEq l y ∨ containsOrEq r y := by
  simp [contains_iff_exists_immediatelyContains, or_and_right, exists_or]

@[simp] theorem containsOrEq_leaf (tok : LIToken) :
    containsOrEq (leaf tok) y ↔ y = leaf tok :=
  reflTransGen_iff_eq (immediatelyContains_leaf tok)

@[simp] theorem containsOrEq_trace : containsOrEq trace y ↔ y = trace :=
  reflTransGen_iff_eq immediatelyContains_trace

@[simp] theorem containsOrEq_traceOf (tok : LIToken) :
    containsOrEq (traceOf tok) y ↔ y = traceOf tok :=
  reflTransGen_iff_eq (immediatelyContains_traceOf tok)

@[simp] theorem containsOrEq_merge :
    containsOrEq (merge l r) y ↔ y = merge l r ∨ containsOrEq l y ∨ containsOrEq r y := by
  rw [containsOrEq_iff_eq_or_contains, contains_merge]

/-! ### The vertex count grades containment -/

theorem numNodes_lt_of_immediatelyContains (h : immediatelyContains x y) :
    y.val.numNodes < x.val.numNodes := by
  obtain ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ := exists_form x <;> simp at h
  obtain rfl | rfl := h <;> simp <;> omega

theorem numNodes_lt_of_contains (h : contains x y) : y.val.numNodes < x.val.numNodes :=
  transGen_minimal (r' := InvImage (· > ·) fun s : SyntacticObject ↦ s.val.numNodes)
    (fun _ _ ↦ numNodes_lt_of_immediatelyContains) x y h

/-- Being a proper term is well-founded: an object has finitely many terms. -/
theorem wellFounded_flip_contains : WellFounded (flip contains) :=
  Subrelation.wf (fun h ↦ numNodes_lt_of_contains h)
    (InvImage.wf (fun s : SyntacticObject ↦ s.val.numNodes) wellFounded_lt)

instance : IsStrictOrder SyntacticObject contains where
  irrefl _ h := lt_irrefl _ (numNodes_lt_of_contains h)
  trans _ _ _ := TransGen.trans

theorem contains_irrefl (x : SyntacticObject) : ¬ contains x x := irrefl x

end SyntacticObject

/-! ### Terms -/

/-- The subtrees of a syntactic object are its terms, hence syntactic objects. -/
theorem isSyntacticObject_of_mem_subtrees (s : SyntacticObject) :
    ∀ m ∈ UnorderedTree.subtrees s.val, IsSyntacticObject m := by
  induction s using SyntacticObject.ind with
  | leaf tok =>
    simp only [SyntacticObject.leaf_val, mem_subtrees_leaf, forall_eq]
    exact (SyntacticObject.leaf tok).2
  | trace =>
    simp only [SyntacticObject.trace_val, mem_subtrees_leaf, forall_eq]
    exact SyntacticObject.trace.2
  | traceOf tok =>
    simp only [SyntacticObject.traceOf_val, mem_subtrees_leaf, forall_eq]
    exact (SyntacticObject.traceOf tok).2
  | merge l r ihl ihr =>
    simp only [SyntacticObject.merge_val, mem_subtrees_node_pair]
    rintro m (rfl | h | h)
    exacts [(SyntacticObject.merge l r).2, ihl m h, ihr m h]

namespace SyntacticObject

variable {x y l r : SyntacticObject}

/-- The terms of a syntactic object, itself included. -/
def terms (s : SyntacticObject) : Multiset SyntacticObject :=
  (UnorderedTree.subtrees s.val).pmap Subtype.mk (isSyntacticObject_of_mem_subtrees s)

@[simp] theorem map_val_terms (s : SyntacticObject) :
    s.terms.map Subtype.val = UnorderedTree.subtrees s.val := by
  simp [terms, Multiset.map_pmap, Multiset.pmap_eq_map]

@[simp] theorem terms_leaf (tok : LIToken) : (leaf tok).terms = {leaf tok} :=
  Multiset.map_injective Subtype.val_injective <| by
    rw [Multiset.map_singleton, map_val_terms, leaf_val, UnorderedTree.subtrees_leaf]

@[simp] theorem terms_trace : trace.terms = {trace} :=
  Multiset.map_injective Subtype.val_injective <| by
    rw [Multiset.map_singleton, map_val_terms, trace_val, UnorderedTree.subtrees_leaf]

@[simp] theorem terms_traceOf (tok : LIToken) : (traceOf tok).terms = {traceOf tok} :=
  Multiset.map_injective Subtype.val_injective <| by
    rw [Multiset.map_singleton, map_val_terms, traceOf_val, UnorderedTree.subtrees_leaf]

@[simp] theorem terms_merge (l r : SyntacticObject) :
    (merge l r).terms = merge l r ::ₘ (l.terms + r.terms) :=
  Multiset.map_injective Subtype.val_injective <| by
    simp only [Multiset.map_cons, Multiset.map_add, map_val_terms, merge_val,
      UnorderedTree.subtrees_node_pair]

/-- The terms of `x` are the objects it reflexively contains. -/
@[simp] theorem mem_terms : y ∈ x.terms ↔ containsOrEq x y := by
  induction x using ind with
  | leaf tok => simp
  | trace => simp
  | traceOf tok => simp
  | merge l r ihl ihr => simp [ihl, ihr]

theorem self_mem_terms (s : SyntacticObject) : s ∈ s.terms :=
  mem_terms.2 ReflTransGen.refl

theorem terms_subset_terms (h : containsOrEq x y) : y.terms ⊆ x.terms :=
  fun _ hz ↦ mem_terms.2 (ReflTransGen.trans h (mem_terms.1 hz))

/-- One term per vertex. -/
theorem card_terms (s : SyntacticObject) : s.terms.card = s.val.numNodes := by
  rw [terms, Multiset.card_pmap, UnorderedTree.card_subtrees]

instance (x y : SyntacticObject) : Decidable (containsOrEq x y) :=
  decidable_of_iff _ mem_terms

/-! ### Accessible terms -/

/-- The accessible terms, the terms at the non-root vertices. -/
def accessibleTerms (s : SyntacticObject) : Multiset SyntacticObject := s.terms.erase s

theorem cons_accessibleTerms (s : SyntacticObject) : s ::ₘ s.accessibleTerms = s.terms :=
  Multiset.cons_erase (self_mem_terms s)

@[simp] theorem accessibleTerms_leaf (tok : LIToken) : (leaf tok).accessibleTerms = 0 := by
  simp [accessibleTerms]

@[simp] theorem accessibleTerms_trace : trace.accessibleTerms = 0 := by
  simp [accessibleTerms]

@[simp] theorem accessibleTerms_traceOf (tok : LIToken) : (traceOf tok).accessibleTerms = 0 := by
  simp [accessibleTerms]

@[simp] theorem accessibleTerms_merge (l r : SyntacticObject) :
    (merge l r).accessibleTerms = l.terms + r.terms := by
  simp [accessibleTerms]

/-- The accessible terms of `x` are the objects it contains. -/
@[simp] theorem mem_accessibleTerms : y ∈ x.accessibleTerms ↔ contains x y := by
  induction x using ind with
  | leaf tok => simp
  | trace => simp
  | traceOf tok => simp
  | merge l r _ _ => simp

/-- One accessible term per edge. -/
theorem card_accessibleTerms (s : SyntacticObject) :
    s.accessibleTerms.card = s.val.numEdges := by
  rw [accessibleTerms, Multiset.card_erase_of_mem (self_mem_terms s), card_terms]; rfl

instance (x y : SyntacticObject) : Decidable (contains x y) :=
  decidable_of_iff _ mem_accessibleTerms

/-! ### C-command -/

variable {root : SyntacticObject}

/-- `x` and `y` are sisters in `root` when they are distinct daughters of some term of
`root`. -/
def areSistersIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.terms, immediatelyContains z x ∧ immediatelyContains z y ∧ x ≠ y

instance (root x y : SyntacticObject) : Decidable (areSistersIn root x y) :=
  Multiset.decidableExistsMultiset

theorem areSistersIn.symm (h : areSistersIn root x y) : areSistersIn root y x :=
  let ⟨z, hz, hx, hy, hne⟩ := h; ⟨z, hz, hy, hx, hne.symm⟩

theorem areSistersIn.mem_left (h : areSistersIn root x y) : x ∈ root.terms :=
  let ⟨_, hz, hx, _, _⟩ := h; mem_terms.2 (ReflTransGen.tail (mem_terms.1 hz) hx)

theorem areSistersIn.mem_right (h : areSistersIn root x y) : y ∈ root.terms :=
  h.symm.mem_left

/-- `x` c-commands `y` in `root` when a sister of `x` contains or equals `y`. -/
def cCommandsIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.terms, areSistersIn root x z ∧ containsOrEq z y

instance (root x y : SyntacticObject) : Decidable (cCommandsIn root x y) :=
  Multiset.decidableExistsMultiset

/-- Sisters c-command each other. -/
theorem cCommandsIn_of_areSistersIn (h : areSistersIn root x y) : cCommandsIn root x y :=
  ⟨y, h.mem_right, h, ReflTransGen.refl⟩

/-- A c-commanded object is a term of the root. -/
theorem mem_terms_of_cCommandsIn (h : cCommandsIn root x y) : y ∈ root.terms :=
  let ⟨_, hz, _, hzy⟩ := h; terms_subset_terms (mem_terms.1 hz) (mem_terms.2 hzy)

/-- The c-command domain of `x` in `root`, the search space of a probe sitting at `x`. -/
def domainIn (root x : SyntacticObject) : Multiset SyntacticObject :=
  root.terms.filter (cCommandsIn root x)

@[simp] theorem mem_domainIn : y ∈ domainIn root x ↔ cCommandsIn root x y :=
  Multiset.mem_filter.trans (and_iff_right_of_imp mem_terms_of_cCommandsIn)

/-- `x` c-commands `y` in `root` and `y` does not c-command `x`. -/
def asymCCommandsIn (root x y : SyntacticObject) : Prop :=
  cCommandsIn root x y ∧ ¬ cCommandsIn root y x

instance (root x y : SyntacticObject) : Decidable (asymCCommandsIn root x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Sisters never asymmetrically c-command each other. -/
theorem not_asymCCommandsIn_of_areSistersIn (h : areSistersIn root x y) :
    ¬ asymCCommandsIn root x y :=
  fun h' ↦ h'.2 (cCommandsIn_of_areSistersIn h.symm)

end SyntacticObject

end Minimalist
