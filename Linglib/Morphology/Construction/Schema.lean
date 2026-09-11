/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.PartialUnify
import Mathlib.Order.Lattice

/-!
# Constructional schemas

This file defines the schemas of Relational Morphology and Construction Morphology, lexical
entries with variables. A schema is a description indexed by slots, valued in a partial order
with a bottom element, together with the set of slots marked as open variables. A slot above
`⊥` is a constant and a slot at `⊥` is a variable, open or closed. An item instantiates a schema
when the description lies below it slot by slot, so the instances of a schema form the principal
upper set of its description, and instantiation is unification against the description.

A schema plays two roles relative to a lexicon of stored items. In its relational role it
motivates an item already stored; in its generative role it licenses a possibly novel item whose
closed variables take only fillers attested among the stored instances. Every related item is
generated, every generated item is related once stored, and a schema is productive, every
variable open, exactly when it generates its own description over the empty lexicon.

## Main declarations

* `Schema`: a slot-indexed description with a set of open variables.
* `Schema.Instantiates`, `Schema.instantiates_iff_unify`: instantiation as pointwise domination,
  equivalently as unification.
* `Schema.Relates`, `Schema.Generates`, `Schema.IsProductive`: the two roles of a schema and
  productivity.
* `Schema.instantiates_inf_iff`, `Schema.instantiates_iff_of_unify_eq_some`: the meet of two
  items is their least general generalization, and the unification of two descriptions has
  exactly their common instances.

## Implementation notes

Productivity is a property of variables rather than of a schema as a whole, so constants are
exempt from attestation and `Schema.IsProductive` is the case in which every variable is open.
Marking a constant slot as open has no effect.

## References

* [jackendoff-audring-2020]
* [booij-2010-compass]
* [plotkin-1970]
* [albright-hayes-2003]
-/

namespace Morphology.Construction

variable {V α : Type*}

/-- A schema is a slot-indexed description `body` together with a set `opens` of slots marked as
open variables. A slot at `⊥` is a variable and a slot above `⊥` is a constant. -/
@[ext]
structure Schema (V α : Type*) where
  /-- The slot-indexed description. -/
  body : V → α
  /-- The slots marked as open variables. -/
  opens : Set V

namespace Schema

section PartialOrder
variable [PartialOrder α] {s t : Schema V α} {w w₁ w₂ : V → α} {Λ Λ' : Set (V → α)}
  {v : V}

/-- An item `w` instantiates a schema `s` if the description of `s` lies below `w` slot by slot:
each constant is matched and each variable is filled freely. -/
def Instantiates (s : Schema V α) (w : V → α) : Prop := s.body ≤ w

/-- A schema instantiates its own description. -/
theorem instantiates_body (s : Schema V α) : s.Instantiates s.body := le_rfl

/-- The instances of a schema form an upper set. -/
theorem Instantiates.trans_le (h : s.Instantiates w₁) (hw : w₁ ≤ w₂) :
    s.Instantiates w₂ :=
  h.trans hw

/-- A schema lies below another exactly when it is instantiated by everything the other is. -/
theorem body_le_body_iff :
    t.body ≤ s.body ↔ ∀ ⦃w⦄, s.Instantiates w → t.Instantiates w :=
  ⟨λ h _ hw => h.trans hw, λ h => h s.instantiates_body⟩

/-- An item instantiates a schema exactly when unifying it with the description returns the
item. -/
theorem instantiates_iff_unify [Fintype V] [PartialUnify α] :
    s.Instantiates w ↔ PartialUnify.unify s.body w = some w := by
  rw [PartialUnify.unify_eq_some_iff_isLUB]
  refine ⟨λ h => ⟨?_, ?_⟩, λ h => h.1 (Set.mem_insert _ _)⟩
  · rintro x (rfl | rfl)
    exacts [h, le_rfl]
  · exact λ _ hu => hu (Set.mem_insert_of_mem _ rfl)

/-- The instances of a unified description are the common instances of its two conjuncts. -/
theorem instantiates_iff_of_unify_eq_some [Fintype V] [PartialUnify α] {u : Schema V α}
    (h : PartialUnify.unify s.body t.body = some u.body) :
    u.Instantiates w ↔ s.Instantiates w ∧ t.Instantiates w := by
  rw [Instantiates, isLUB_le_iff (PartialUnify.isLUB_of_unify_eq_some h),
    PartialUnify.mem_upperBounds_pair]
  rfl

/-! ### The relational role -/

/-- A schema `s` relates an item `w` over a lexicon `Λ` if `w` is stored in `Λ` and instantiates
`s`: the relational role of a schema. -/
def Relates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  w ∈ Λ ∧ s.Instantiates w

theorem Relates.instantiates (h : s.Relates Λ w) : s.Instantiates w := h.2

theorem Relates.mono (h : Λ ⊆ Λ') (hw : s.Relates Λ w) : s.Relates Λ' w := ⟨h hw.1, hw.2⟩

/-- An instance, once stored, is related by the schema. -/
theorem Instantiates.relates_insert (h : s.Instantiates w) : s.Relates (insert w Λ) w :=
  ⟨Set.mem_insert _ _, h⟩

/-- The fillers attested at a slot `v` are the values the stored instances of `s` take there:
the filler list of a closed variable, derived from the lexicon rather than stipulated. -/
def attested (s : Schema V α) (Λ : Set (V → α)) (v : V) : Set α :=
  {a | ∃ w, s.Relates Λ w ∧ w v = a}

@[simp]
theorem mem_attested {a : α} : a ∈ s.attested Λ v ↔ ∃ w, s.Relates Λ w ∧ w v = a :=
  Iff.rfl

theorem Relates.apply_mem_attested (h : s.Relates Λ w) (v : V) : w v ∈ s.attested Λ v :=
  ⟨w, h, rfl⟩

theorem attested_mono (h : Λ ⊆ Λ') (v : V) : s.attested Λ v ⊆ s.attested Λ' v := by
  rintro a ⟨w, hw, rfl⟩
  exact ⟨w, hw.mono h, rfl⟩

end PartialOrder

/-- A schema is instantiated by the meet of two items exactly when it is instantiated by both:
the meet is their least general generalization. -/
theorem instantiates_inf_iff [SemilatticeInf α] {s : Schema V α} {w₁ w₂ : V → α} :
    s.Instantiates (w₁ ⊓ w₂) ↔ s.Instantiates w₁ ∧ s.Instantiates w₂ :=
  le_inf_iff

/-! ### The generative role -/

section OrderBot
variable [PartialOrder α] [OrderBot α] {s : Schema V α} {w : V → α} {Λ Λ' : Set (V → α)}

/-- A schema `s` generates an item `w` over a lexicon `Λ` if `w` instantiates `s` and every closed
variable of `s`, a slot at `⊥` not marked open, takes in `w` a filler attested in `Λ`: the
generative role of a schema, licensing possibly novel items. -/
def Generates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  s.Instantiates w ∧ ∀ v, s.body v = ⊥ → v ∉ s.opens → w v ∈ s.attested Λ v

theorem Generates.instantiates (h : s.Generates Λ w) : s.Instantiates w := h.1

/-- A related item is generated, attesting its own fillers. -/
theorem Relates.generates (h : s.Relates Λ w) : s.Generates Λ w :=
  ⟨h.2, λ v _ _ => h.apply_mem_attested v⟩

/-- A generated item, once stored, is related by the schema. -/
theorem Generates.relates_insert (h : s.Generates Λ w) : s.Relates (insert w Λ) w :=
  h.instantiates.relates_insert

/-- Generation is monotone in the lexicon. -/
theorem Generates.mono (h : Λ ⊆ Λ') (hw : s.Generates Λ w) : s.Generates Λ' w :=
  ⟨hw.1, λ v hv hvo => attested_mono h v (hw.2 v hv hvo)⟩

/-- A schema is productive if every variable, every slot at `⊥`, is open. -/
def IsProductive (s : Schema V α) : Prop := ∀ v, s.body v = ⊥ → v ∈ s.opens

/-- A productive schema generates exactly its instances. -/
theorem IsProductive.generates_iff (hs : s.IsProductive) :
    s.Generates Λ w ↔ s.Instantiates w :=
  ⟨Generates.instantiates, λ h => ⟨h, λ v hv hvo => absurd (hs v hv) hvo⟩⟩

/-- A schema is productive exactly when it generates its own description over the empty
lexicon. -/
theorem isProductive_iff_generates_empty : s.IsProductive ↔ s.Generates ∅ s.body := by
  refine ⟨λ hs => ⟨le_rfl, λ v hv hvo => absurd (hs v hv) hvo⟩, λ h v hv => ?_⟩
  by_contra hvo
  obtain ⟨w, ⟨hw, -⟩, -⟩ := h.2 v hv hvo
  exact hw

end OrderBot

end Schema

end Morphology.Construction
