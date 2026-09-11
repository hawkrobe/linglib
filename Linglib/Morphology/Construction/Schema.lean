/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.PartialUnify
import Mathlib.Order.Lattice

/-!
# Constructional schemas

This file defines the schemas of Relational Morphology ([jackendoff-audring-2020]): lexical
entries with variables. A schema is a slot-indexed description `body : V → α` over a partial
order with a bottom, together with the set `opens` of slots marked as open variables. A slot
pinned above `⊥` is a constant; a slot at `⊥` is a variable, open (freely fillable) or closed
(filled only from a learned list). An item instantiates a schema when the description
dominates it pointwise (`Schema.Instantiates`), so the instances of a schema are the principal
upper set `Set.Ici s.body` of the Pi order, and instantiation is unification against the
description (`Schema.instantiates_iff_unify`).

The two roles of a schema are relative to a stored lexicon `Λ`. In its relational role
(`Schema.Relates`) a schema motivates an item already stored; in its generative role
(`Schema.Generates`) it licenses a possibly novel item whose closed variables take only fillers
attested in `Λ` (`Schema.attested`). A closed variable's filler list is derived from the lexicon
rather than stipulated, since a nonproductive schema has all its instances listed. The
Relational Hypothesis of [jackendoff-audring-2020] is then a chain of inclusions: a related
item is generated (`Schema.Relates.generates`), a generated item is related once committed to
memory (`Schema.Generates.relates_insert`), and a schema is productive, every variable open,
exactly when it generates its own description from an empty lexicon
(`Schema.isProductive_iff_generates_empty`).

Two order-theoretic facts carry the constructional operations of [booij-2010-compass].
Unifying two descriptions gives the schema whose instances are exactly the common instances
(`Schema.instantiates_iff_of_unify_eq_some`). A schema is instantiated by the pointwise meet of
two items exactly when it is instantiated by both (`Schema.instantiates_inf_iff`), which makes
the meet their least general generalization ([plotkin-1970]; the minimal generalization of
[albright-hayes-2003]).

## Main declarations

* `Schema`: a slot-indexed description with a set of open variables.
* `Schema.Instantiates`, `Schema.instantiates_iff_unify`: instantiation as pointwise
  domination, equivalently as unification.
* `Schema.Relates`, `Schema.Generates`, `Schema.attested`: the lexicon-relative roles.
* `Schema.IsProductive`, `Schema.isProductive_iff_generates_empty`: productivity as generation
  from an empty lexicon.

## Implementation notes

Productivity is a property of variables rather than of a schema as a whole, and
`Schema.IsProductive` is the derived case in which every variable is open. Constants are exempt
from the attestation condition of `Schema.Generates`, so a schema whose variables are all open
generates over any lexicon, the empty one included. Marking a constant slot as open is
harmless: the slot is not a variable, so it is never subject to attestation.

## References

* [jackendoff-audring-2020]
* [booij-2010-compass]
* [plotkin-1970]
* [albright-hayes-2003]
-/

namespace Morphology.Construction

variable {V α : Type*}

/-- A schema: a slot-indexed description `body` together with the slots `opens` marked as open
variables. A slot at `⊥` is a variable; a slot above `⊥` is a constant. -/
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

/-- An item `w` instantiates a schema when the description dominates `w` slot by slot: each
constant is matched and each variable is filled freely. -/
def Instantiates (s : Schema V α) (w : V → α) : Prop := s.body ≤ w

/-- A schema instantiates its own description. -/
theorem instantiates_body (s : Schema V α) : s.Instantiates s.body := le_rfl

/-- The instances of a schema are closed upward. -/
theorem Instantiates.trans_le (h : s.Instantiates w₁) (hw : w₁ ≤ w₂) :
    s.Instantiates w₂ :=
  h.trans hw

/-- A schema dominated by another is instantiated by everything the other is: the subschema
relation is pointwise domination of descriptions. -/
theorem body_le_body_iff :
    t.body ≤ s.body ↔ ∀ ⦃w⦄, s.Instantiates w → t.Instantiates w :=
  ⟨λ h _ hw => h.trans hw, λ h => h s.instantiates_body⟩

/-- Instantiation is unification against the description: `w` instantiates `s` exactly when
unifying the description with `w` succeeds and returns `w`. -/
theorem instantiates_iff_unify [Fintype V] [PartialUnify α] :
    s.Instantiates w ↔ PartialUnify.unify s.body w = some w := by
  rw [PartialUnify.unify_eq_some_iff_isLUB]
  refine ⟨λ h => ⟨?_, ?_⟩, λ h => h.1 (Set.mem_insert _ _)⟩
  · rintro x (rfl | rfl)
    exacts [h, le_rfl]
  · exact λ _ hu => hu (Set.mem_insert_of_mem _ rfl)

/-- Unifying two descriptions gives the schema whose instances are exactly the common
instances of the two. -/
theorem instantiates_iff_of_unify_eq_some [Fintype V] [PartialUnify α] {u : Schema V α}
    (h : PartialUnify.unify s.body t.body = some u.body) :
    u.Instantiates w ↔ s.Instantiates w ∧ t.Instantiates w := by
  rw [Instantiates, isLUB_le_iff (PartialUnify.isLUB_of_unify_eq_some h),
    PartialUnify.mem_upperBounds_pair]
  rfl

/-! ### The relational role -/

/-- The relational role: `s` motivates the item `w` stored in `Λ`. -/
def Relates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  w ∈ Λ ∧ s.Instantiates w

theorem Relates.instantiates (h : s.Relates Λ w) : s.Instantiates w := h.2

theorem Relates.mono (h : Λ ⊆ Λ') (hw : s.Relates Λ w) : s.Relates Λ' w := ⟨h hw.1, hw.2⟩

/-- Any instance, once stored, is related by the schema. -/
theorem Instantiates.relates_insert (h : s.Instantiates w) : s.Relates (insert w Λ) w :=
  ⟨Set.mem_insert _ _, h⟩

/-- The fillers attested at slot `v`: the values the stored instances of `s` take there. A
closed variable's filler list, derived from the lexicon rather than stipulated. -/
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

/-- A schema is instantiated by the pointwise meet of two items exactly when it is instantiated
by both: the meet is the least general generalization of the two. -/
theorem instantiates_inf_iff [SemilatticeInf α] {s : Schema V α} {w₁ w₂ : V → α} :
    s.Instantiates (w₁ ⊓ w₂) ↔ s.Instantiates w₁ ∧ s.Instantiates w₂ :=
  le_inf_iff

/-! ### The generative role -/

section OrderBot
variable [PartialOrder α] [OrderBot α] {s : Schema V α} {w : V → α} {Λ Λ' : Set (V → α)}

/-- The generative role: `s` licenses a possibly novel item `w` whose closed variables, the
slots at `⊥` not marked open, take only fillers attested in `Λ`. -/
def Generates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  s.Instantiates w ∧ ∀ v, s.body v = ⊥ → v ∉ s.opens → w v ∈ s.attested Λ v

theorem Generates.instantiates (h : s.Generates Λ w) : s.Instantiates w := h.1

/-- A stored instance is generated: it attests its own fillers. -/
theorem Relates.generates (h : s.Relates Λ w) : s.Generates Λ w :=
  ⟨h.2, λ v _ _ => h.apply_mem_attested v⟩

/-- The memory-collapse step of the Relational Hypothesis: a generated item, once committed to
memory, falls under the schema's relational role. -/
theorem Generates.relates_insert (h : s.Generates Λ w) : s.Relates (insert w Λ) w :=
  h.instantiates.relates_insert

/-- Generation grows with the lexicon. -/
theorem Generates.mono (h : Λ ⊆ Λ') (hw : s.Generates Λ w) : s.Generates Λ' w :=
  ⟨hw.1, λ v hv hvo => attested_mono h v (hw.2 v hv hvo)⟩

/-- A schema is productive when every variable is open. Productivity is a property of
variables rather than of the schema as a whole; this is the fully open case. -/
def IsProductive (s : Schema V α) : Prop := ∀ v, s.body v = ⊥ → v ∈ s.opens

/-- A productive schema generates every instance, having no closed variable to confine. -/
theorem IsProductive.generates_iff (hs : s.IsProductive) :
    s.Generates Λ w ↔ s.Instantiates w :=
  ⟨Generates.instantiates, λ h => ⟨h, λ v hv hvo => absurd (hs v hv) hvo⟩⟩

/-- A schema is productive exactly when it generates its own description from an empty
lexicon: with nothing stored, no closed variable can be filled. -/
theorem isProductive_iff_generates_empty : s.IsProductive ↔ s.Generates ∅ s.body := by
  refine ⟨λ hs => ⟨le_rfl, λ v hv hvo => absurd (hs v hv) hvo⟩, λ h v hv => ?_⟩
  by_contra hvo
  obtain ⟨w, ⟨hw, -⟩, -⟩ := h.2 v hv hvo
  exact hw

end OrderBot

end Schema

end Morphology.Construction
