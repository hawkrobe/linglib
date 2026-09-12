/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.ConstructionMorphology.Schema
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.WellFounded
import Mathlib.Data.Option.Basic

/-!
# Inheritance hierarchies

This file defines default inheritance with override: a lexical entry inherits a property from a
more general entry unless it specifies the property itself. It is the organizing principle of
the hierarchical lexicon of Construction Morphology and the rival to relational motivation in
Relational Morphology. A `Hierarchy` is a single-parent forest whose parent relation is
well-founded, and `Hierarchy.value` looks up a node's own specification if it has one and its
nearest ancestor's otherwise, by recursion along the parent relation; the recursion step is
the priority union of partial values, `Option.or`.

A finite family of schemas with distinct descriptions carries its own hierarchy
(`Hierarchy.ofFamily`): a schema's parent is the nearest more general schema of the family,
the one whose description is greatest among those strictly below its own. What is inherited
monotonically, everything a more general description pins, needs no lookup, since an instance
of a schema instantiates every more general schema; the lookup is for defeasible properties
that a subschema may override.

Multiple inheritance, a node with two parents, is not modelled here; the multi-parent form of
the override step is `Syntax/ConstructionGrammar/Inheritance.lean`. The formal traditions of
defaults with override are DATR and Network Morphology.

## Main declarations

* `Hierarchy`, `Hierarchy.ofDepth`: a single-parent forest with a well-founded parent relation.
* `Hierarchy.value`, `Hierarchy.value_eq`: default-and-override lookup and its recursion.
* `Hierarchy.parent_asymm`: no two nodes are each other's parent.
* `Hierarchy.NearestGeneral`, `Hierarchy.ofFamily`, `Hierarchy.ofFamily_parent_eq_some_iff`: the
  hierarchy derived from a finite family of schemas.

## References

* [jackendoff-audring-2020]
* [booij-2010-compass]
* [evans-gazdar-1996]
* [brown-hippisley-2012]
-/

namespace ConstructionMorphology

variable {ι β : Type*}

/-- A single-parent inheritance hierarchy: `parent` links each node to its immediate
supertype, `none` at a root, and `wf` witnesses acyclicity. -/
structure Hierarchy (ι : Type*) where
  /-- The immediate-supertype map. -/
  parent : ι → Option ι
  /-- Acyclicity: the parent relation is well-founded. -/
  wf : WellFounded λ a b => parent b = some a

namespace Hierarchy

/-- A hierarchy from a parent map and a depth function decreasing toward the root; on a finite
node type the obligation closes by `decide`. -/
def ofDepth (parent : ι → Option ι) (depth : ι → ℕ)
    (h : ∀ a b, parent b = some a → depth a < depth b) : Hierarchy ι where
  parent := parent
  wf := Subrelation.wf (λ {a b} hab => h a b hab) (InvImage.wf depth Nat.lt_wfRel.wf)

variable (h : Hierarchy ι) {att : ι → Option β}

/-- Default-and-override lookup: a node's own specification if present, else the nearest
ancestor's, by recursion along the parent relation. -/
def value (att : ι → Option β) : ι → Option β :=
  h.wf.fix λ n ih => (att n).or ((h.parent n).pbind λ m hm => ih m (Option.mem_def.1 hm))

/-- The recursion step is the priority union: the local specification wins, else defer to the
parent. -/
theorem value_eq (n : ι) : h.value att n = (att n).or ((h.parent n).bind (h.value att)) := by
  rw [value, WellFounded.fix_eq, Option.pbind_eq_bind]

/-- Override wins: a local specification is the value. -/
theorem value_eq_of_att {n : ι} {v : β} (hn : att n = some v) : h.value att n = some v := by
  rw [value_eq, hn, Option.some_or]

/-- Path extension: at a node with no local specification, the value is the parent's. -/
theorem value_eq_parent {n : ι} (hn : att n = none) :
    h.value att n = (h.parent n).bind (h.value att) := by
  rw [value_eq, hn, Option.none_or]

/-- No two nodes are each other's parent. -/
theorem parent_asymm {a b : ι} (hab : h.parent a = some b) (hba : h.parent b = some a) :
    False :=
  h.wf.asymmetric a b hba hab

/-! ### The hierarchy of a family of schemas -/

section Family
variable {V α : Type*} [PartialOrder α] {family : ι → Schema V α} {i j : ι}

/-- `j` is the nearest more general schema than `i` in the family when its description is
strictly below `i`'s and above every other description of the family strictly below `i`'s. -/
def NearestGeneral (family : ι → Schema V α) (i j : ι) : Prop :=
  (family j).body < (family i).body ∧
    ∀ k, (family k).body < (family i).body → (family k).body ≤ (family j).body

/-- With distinct descriptions, the nearest more general schema is unique. -/
theorem NearestGeneral.unique (hinj : Function.Injective λ i => (family i).body) {j' : ι}
    (hj : NearestGeneral family i j) (hj' : NearestGeneral family i j') : j = j' :=
  hinj (le_antisymm (hj'.2 j hj.1) (hj.2 j' hj'.1))

variable [Fintype ι] [DecidableLE (V → α)] [DecidableLT (V → α)]

instance (family : ι → Schema V α) (i j : ι) : Decidable (NearestGeneral family i j) := by
  unfold NearestGeneral
  infer_instance

/-- The subsumption hierarchy of a finite family of schemas with distinct descriptions: a
schema's parent is the nearest more general schema of the family, when there is one. -/
def ofFamily (family : ι → Schema V α) (hinj : Function.Injective λ i => (family i).body) :
    Hierarchy ι where
  parent i :=
    if h : ∃ j, NearestGeneral family i j then
      some (Finset.univ.choose (NearestGeneral family i)
        (h.elim λ j hj => ⟨j, ⟨Finset.mem_univ _, hj⟩, λ j' hj' => hj'.2.unique hinj hj⟩))
    else none
  wf := by
    have hT : IsTrans ι λ a b => (family a).body < (family b).body := ⟨λ _ _ _ => lt_trans⟩
    have hI : Std.Irrefl λ a b => (family a).body < (family b).body := ⟨λ _ => lt_irrefl _⟩
    refine Subrelation.wf ?_
      (Finite.wellFounded_of_trans_of_irrefl λ a b => (family a).body < (family b).body)
    intro a b hab
    split_ifs at hab with h
    exact (Option.some_inj.1 hab ▸
      (Finset.choose_spec (NearestGeneral family b) Finset.univ _).2).1

theorem ofFamily_parent_eq_some_iff (hinj : Function.Injective λ i => (family i).body) :
    (ofFamily family hinj).parent i = some j ↔ NearestGeneral family i j := by
  show (if h : ∃ j, NearestGeneral family i j then some (Finset.univ.choose _ _) else none) =
      some j ↔ _
  split_ifs with h
  · rw [Option.some_inj]
    exact ⟨λ e => e ▸ (Finset.choose_spec (NearestGeneral family i) Finset.univ _).2,
      λ hj => ((Finset.choose_spec (NearestGeneral family i) Finset.univ _).2).unique hinj hj⟩
  · exact iff_of_false (by simp) λ hj => h ⟨j, hj⟩

theorem ofFamily_parent_eq_none_iff (hinj : Function.Injective λ i => (family i).body) :
    (ofFamily family hinj).parent i = none ↔ ¬ ∃ j, NearestGeneral family i j := by
  show (if h : ∃ j, NearestGeneral family i j then some (Finset.univ.choose _ _) else none) =
      none ↔ _
  split_ifs with h <;> simp [h]

end Family

end Hierarchy

end ConstructionMorphology
