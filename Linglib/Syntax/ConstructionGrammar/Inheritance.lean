/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.Flat
import Linglib.Syntax.ConstructionGrammar.Basic

/-!
# Constructional inheritance

Computational content for the two modes of constructional inheritance
distinguished by [goldberg-1995] §3.3.1 (the `InheritanceMode` enum in
`ConstructionGrammar.Basic`), grounded in the flat feature-slot order:
in the **complete mode** representations must strictly unify (`Compat`,
`PartialUnify.unify` — the regime [kay-fillmore-1999] built their formal
CxG on and [sag-2012]'s SBCG inherits from HPSG), while in the **default
mode** the inheriting construction overrides its parents ([diessel-2023]
Table 2; the default-unification tradition of
[lascarides-copestake-1999]): `inheritField` is the priority union
(`Flat.or`) of the child's slot with its parents' unification
(`PartialUnify.unifyList`), so a parental conflict the child does not
legislate leaves the slot unspecified.

## Main declarations

- `inheritField`, `ResolvesField`: default-mode slot semantics
- `inheritField_of_compat`: the two modes agree absent conflict
- `Constructicon.parentsOf`, `derivedSpec`, `ResolvesAll`, `WellFormed`:
  inheritance computed through a constructicon's links, generic in the
  specification type
- `inheritFieldUnique`, `Constructicon.derivedField`: inheritance for
  slots without decidable equality (e.g. denotations)
-/

namespace ConstructionGrammar

open PartialUnify (unifyList unifyList_pair unify_eq_none_iff)

/-! ### Default-mode slot algebra

A specification slot is a `Flat`-ordered partial value: `⊥` is
"unspecified", and inheritance fills unspecified slots from parents. -/

section FieldAlgebra

variable {α : Type*} [DecidableEq α]

/-- Normal-mode (default) inheritance for one slot ([goldberg-1995]
§3.3.1; [diessel-2023] Table 2: "low-level representations override
high-level representations if there is a conflict";
[lascarides-copestake-1999]): the inheriting construction's own value
wins; an unspecified slot takes its parents' unification when it exists;
a parental conflict the child does not legislate leaves the slot
unspecified. -/
def inheritField (own : Flat α) (parents : List (Flat α)) : Flat α :=
  own.or ((unifyList parents).getD ⊥)

/-- The child legislates wherever its parents conflict — [goldberg-1995]'s
normal mode: "conflicts are addressed by the inheriting construction,
which specifies its own constraints". -/
def ResolvesField (own : Flat α) (parents : List (Flat α)) : Prop :=
  unifyList parents = none → own ≠ ⊥

instance (own : Flat α) (parents : List (Flat α)) :
    Decidable (ResolvesField own parents) :=
  inferInstanceAs (Decidable (_ → _))

@[simp]
theorem inheritField_coe (a : α) (parents : List (Flat α)) :
    inheritField ↑a parents = ↑a := rfl

@[simp]
theorem inheritField_nil (own : Flat α) : inheritField own [] = own := by
  simp [inheritField]

/-- Absent conflict, normal-mode inheritance agrees with strict
(complete-mode) unification: with compatible parents the inherited value
is the priority union of child and parents. Normal mode departs from
complete inheritance only at genuine conflicts. -/
theorem inheritField_of_compat (own : Flat α) {p q : Flat α}
    (h : Compat p q) : inheritField own [p, q] = (own.or p).or q := by
  simp only [inheritField, unifyList_pair,
    Flat.unify_eq_some_or_of_compat h, Option.getD_some]
  exact (Flat.or_assoc own p q).symm

/-- Compatible parents impose no resolution burden on the child. -/
theorem resolvesField_of_compat (own : Flat α) {p q : Flat α}
    (h : Compat p q) : ResolvesField own [p, q] := by
  intro hnone
  rw [unifyList_pair, unify_eq_none_iff] at hnone
  exact absurd h hnone

end FieldAlgebra

/-! ### Inheritance through a constructicon

A specification assignment maps each construction to its *own*
(conflict-resolving) specification; the network then computes each
construction's full specification by normal-mode inheritance from the
parents its links name. The walk is generic in the specification type:
record-valued specifications supply their componentwise `inherit` and
`Resolves` lifts. -/

variable {Sem σ : Type*}

/-- The constructions a network's links name as parents of `name`. -/
def Constructicon.parentsOf (cx : Constructicon Sem) (name : String) :
    List (Construction Sem) :=
  (cx.links.filter (·.child == name)).filterMap
    (λ l => cx.constructions.find? (·.name == l.parent))

/-- The constructions a network's links name as children of `name`. -/
def Constructicon.childrenOf (cx : Constructicon Sem) (name : String) :
    List (Construction Sem) :=
  (cx.links.filter (·.parent == name)).filterMap
    (λ l => cx.constructions.find? (·.name == l.child))

/-- Every link endpoint resolves to a construction in the network — no
dangling name-keyed links. -/
def Constructicon.WellFormed (cx : Constructicon Sem) : Prop :=
  ∀ l ∈ cx.links,
    (∃ c ∈ cx.constructions, c.name = l.parent) ∧
    (∃ c ∈ cx.constructions, c.name = l.child)

instance (cx : Constructicon Sem) : Decidable cx.WellFormed :=
  inferInstanceAs (Decidable (∀ l ∈ _, _ ∧ _))

/-- Normal-mode derived specification of `c` in the network: `c`'s own
specification wins; fields it leaves open are filled from the parents its
links name ([diessel-2023] Table 2's default mode, computed over the
links rather than stipulated per node). -/
def Constructicon.derivedSpec (cx : Constructicon Sem)
    (inherit : σ → List σ → σ) (own : Construction Sem → σ)
    (c : Construction Sem) : σ :=
  inherit (own c) ((cx.parentsOf c.name).map own)

/-- Normal-mode well-formedness of the whole network: every construction
legislates every field its parents conflict on. -/
def Constructicon.ResolvesAll (cx : Constructicon Sem)
    (resolves : σ → List σ → Prop) (own : Construction Sem → σ) : Prop :=
  ∀ c ∈ cx.constructions, resolves (own c) ((cx.parentsOf c.name).map own)

instance (cx : Constructicon Sem) (resolves : σ → List σ → Prop)
    [∀ o ps, Decidable (resolves o ps)] (own : Construction Sem → σ) :
    Decidable (cx.ResolvesAll resolves own) :=
  inferInstanceAs (Decidable (∀ c ∈ _, _))

/-! ### Inheritance of denotation-valued fields

Denotations (e.g. `PartialProp`-valued pragmatic contributions) have no
decidable equality, so agreeing parents cannot be reconciled by
unification. `inheritFieldUnique` inherits when exactly one parent
supplies a value — sufficient for single-mother inheritance, the
configuration of conventional-subtype links. -/

/-- Normal-mode inheritance for one field without decidable equality:
the child's own value wins; an unspecified field takes the value of the
unique supplying parent; multiple suppliers (which `inheritField` could
reconcile when they agree) yield `none`. -/
def inheritFieldUnique {α : Type*} (own : Option α)
    (parents : List (Option α)) : Option α :=
  match own, parents.filterMap id with
  | some x, _ => some x
  | none, [x] => some x
  | none, _ => none

/-- Derived value of a denotation-valued field for `c` in the network:
`c`'s own value wins; otherwise the value of the unique supplying
parent. -/
def Constructicon.derivedField {α : Type*} (cx : Constructicon Sem)
    (own : Construction Sem → Option α) (c : Construction Sem) : Option α :=
  inheritFieldUnique (own c) ((cx.parentsOf c.name).map own)

end ConstructionGrammar
