/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.PartialUnify
import Mathlib.Order.Lattice

/-!
# Constructional schemas

A schema in the sense of [jackendoff-audring-2020] is a lexical entry with
variables: a slot-indexed description `body : V → α` over a bundle of typed
slots, together with the subset `opens` of slots marked open. A slot pinned
above `⊥` is a constant; a slot at `⊥` is a variable, open (freely fillable)
or closed (a learned list of fillers). Instantiation is domination in the
pointwise order (`Schema.Instantiates`), which is unification against the
description (`instantiates_iff_unify`, wiring to `Core.Order.PartialUnify`).

The relational and generative roles a schema can play ([jackendoff-audring-2020]
§2.11) are lexicon-relative: over a stored lexicon `Λ`, `Relates` records a
schema motivating a stored item, `Generates` licenses a possibly-novel item
whose closed slots stay within the fillers `attested` in `Λ`. A closed
variable's filler list is not a second stipulated field — it is derived from
`Λ`, since nonproductive schemas have all their instances listed in the lexicon.
`generates_relates_insert` is the memory-collapse step of that section's
argument: a generated word, once committed to memory, falls under the schema's
relational role.

Structural intersection is the pointwise meet (`instantiates_inf`); the least
general generalization of a filler set is the dual of unification
([plotkin-1970]'s lgg, [albright-hayes-2003]'s minimal generalization),
recorded here as the order-theoretic content without minting new algebra.

## Main declarations

- `Schema` — a slot-indexed description with an open-variable set
- `Schema.Instantiates`, `instantiates_iff_unify` — domination as unification
- `Schema.attested`, `Schema.Relates`, `Schema.Generates` — lexicon-relative roles
- `Schema.instantiates_relates_insert`, `Schema.generates_relates_insert` — the
  memory-collapse step
- `Schema.IsProductive`, `Schema.IsProductive.generates_of_instantiates` — a
  fully open schema generates any instance
- `Schema.instantiates_inf` — structural intersection is instantiated by each conjunct
-/

namespace Morphology.Construction

variable {V α : Type*}

/-- A schema: a slot-indexed description `body`, with `opens` the slots marked as
open variables. A slot at `⊥` is a variable; a slot above `⊥` is a constant. -/
structure Schema (V : Type*) (α : Type*) [PartialOrder α] where
  /-- The slot-indexed description. -/
  body : V → α
  /-- The slots marked as open variables. -/
  opens : Set V

namespace Schema

section PartialOrder
variable [PartialOrder α]

/-- A schema is instantiated by a filling `w` when its description dominates `w`
slot-by-slot: every pinned slot's constraint is met and variables are free. -/
def Instantiates (s : Schema V α) (w : V → α) : Prop := s.body ≤ w

/-- Instantiation is unification against the description: `w` instantiates `s`
exactly when unifying the description with `w` succeeds and returns `w`. -/
theorem instantiates_iff_unify [Fintype V] [PartialUnify α] {s : Schema V α}
    {w : V → α} : s.Instantiates w ↔ PartialUnify.unify s.body w = some w := by
  rw [PartialUnify.unify_eq_some_iff_isLUB]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => h.1 (Set.mem_insert _ _)⟩
  · rintro x (rfl | rfl)
    exacts [h, le_rfl]
  · exact fun _ hu => hu (Set.mem_insert_of_mem _ rfl)

/-- The fillers attested at a slot: the values a stored instance of `s` in `Λ`
takes there. A closed variable's filler list, derived from storage rather than
stipulated separately. -/
def attested (s : Schema V α) (Λ : Set (V → α)) (v : V) : Set α :=
  {a | ∃ w ∈ Λ, s.Instantiates w ∧ w v = a}

/-- The relational role ([jackendoff-audring-2020] §2.11): `s` motivates the
stored item `w`. -/
def Relates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  w ∈ Λ ∧ s.Instantiates w

/-- The generative role ([jackendoff-audring-2020] §2.11): `s` licenses a
possibly-novel item `w` whose closed slots take only attested fillers. -/
def Generates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  s.Instantiates w ∧ ∀ v ∉ s.opens, w v ∈ s.attested Λ v

/-- Any instance, once added to the lexicon, is related by the schema. -/
theorem instantiates_relates_insert {s : Schema V α} {Λ : Set (V → α)} {w : V → α}
    (h : s.Instantiates w) : s.Relates (insert w Λ) w :=
  ⟨Set.mem_insert _ _, h⟩

/-- The memory-collapse step of [jackendoff-audring-2020]'s §2.11 argument: a
generated word, once committed to memory, falls under the schema's relational
role. -/
theorem generates_relates_insert {s : Schema V α} {Λ : Set (V → α)} {w : V → α}
    (h : s.Generates Λ w) : s.Relates (insert w Λ) w :=
  instantiates_relates_insert h.1

/-- A schema is productive when every slot is open — a fully general pattern
with no learned filler lists. -/
def IsProductive (s : Schema V α) : Prop := ∀ v, v ∈ s.opens

/-- A productive schema generates every instance ([jackendoff-audring-2020]: a
productive schema has "gone viral"), since it has no closed slots to confine. -/
theorem IsProductive.generates_of_instantiates {s : Schema V α} {Λ : Set (V → α)}
    {w : V → α} (hp : s.IsProductive) (h : s.Instantiates w) : s.Generates Λ w :=
  ⟨h, fun v hv => absurd (hp v) hv⟩

end PartialOrder

/-- Structural intersection is instantiated by each conjunct: the pointwise meet
of two fillers is a schema they both instantiate — the lower-bound face of the
least general generalization. -/
theorem instantiates_inf [SemilatticeInf α] {w₁ w₂ : V → α} {opens : Set V} :
    Instantiates ⟨w₁ ⊓ w₂, opens⟩ w₁ :=
  inf_le_left

/-! ### Productivity is a genuine restriction

A schema with a closed slot relates its stored instance but cannot generate a
fresh filler for that slot. Generation over the function type `V → α` is an
existential with no `Decidable` instance, so nonproductivity is witnessed
structurally. -/

/-- A stored instance is related by the schema. -/
example : (⟨fun _ => (0 : ℕ), ∅⟩ : Schema Unit ℕ).Relates {fun _ => 0} (fun _ => 0) :=
  ⟨rfl, le_rfl⟩

/-- The same closed-slot schema does not generate an unattested filler. -/
example : ¬ (⟨fun _ => (0 : ℕ), ∅⟩ : Schema Unit ℕ).Generates {fun _ => 0} (fun _ => 1) := by
  rintro ⟨-, hgen⟩
  have h := hgen () (by simp)
  simp only [attested, Set.mem_setOf_eq, Set.mem_singleton_iff] at h
  obtain ⟨w, rfl, -, hwv⟩ := h
  simp at hwv

end Schema

end Morphology.Construction
