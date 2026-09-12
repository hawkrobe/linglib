/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
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

Multiple inheritance, a node with two parents, is not modelled here; the multi-parent form of
the override step is `Syntax/ConstructionGrammar/Inheritance.lean`. The formal traditions of
defaults with override are DATR and Network Morphology.

## Main declarations

* `Hierarchy`, `Hierarchy.ofDepth`: a single-parent forest with a well-founded parent relation.
* `Hierarchy.value`, `Hierarchy.value_eq`: default-and-override lookup and its recursion.
* `Hierarchy.parent_asymm`: no two nodes are each other's parent.

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

end Hierarchy

end ConstructionMorphology
