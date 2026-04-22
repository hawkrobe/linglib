/-
# Discourse Referents

Types for individual, propositional, and concept discourse referents.

Individual and propositional drefs follow @cite{hofmann-2025} "Anaphoric
accessibility with flat update". Concept drefs and the mass/count feature
follow @cite{krifka-2026} "Anaphora for Concepts, Kinds, and Parts in
Dynamic Interpretation".

## Key Types

| Type | Description |
|------|-------------|
| `Entity E` | Entity with universal falsifier ⋆ |
| `MassCount` | Morphosyntactic [MASS] vs [COUNT] feature |
| `ConceptDRef W E` | Concept dref: property + count feature |
| `DRefVal W E` | Heterogeneous dref value (entity / concept / index) |
| `IDref W E` | Individual dref (assignment → world → entity) |
| `PDref W E` | Propositional dref (assignment → set of worlds) |

## The Universal Falsifier ⋆

In Hofmann's system, individual drefs map to ⋆ (star) in worlds where the
referent doesn't exist. For example, in "There's no bathroom", the bathroom
variable maps to ⋆ in all worlds.

The falsifier ⋆ satisfies: R(⋆) = false for all predicates R.

## Concept Discourse Referents

@cite{krifka-2026} proposes that head nouns introduce concept drefs alongside
entity drefs. For example, *dog* in *a dog* introduces a concept dref anchored
to the property `λi.λx[dog(i)(x)]` with a [COUNT] feature. Kind anaphors
(*it* for [MASS], *they* for [COUNT]) pick up concept drefs and derive kind
individuals via Chierchia's ∩ operator. Concept drefs project past anaphoric
islands (negation, modals, conditionals) — they behave like names.

## Propositional Drefs as Local Contexts

ICDRT extends DRT with propositional discourse referents:
- Individual drefs: track what an expression refers to
- Propositional drefs: track where the dref was introduced (local context)

This separation enables anaphora to indefinites under negation:
"Either there's no bathroom, or it's upstairs."

-/

import Linglib.Core.Lexical.Word
import Linglib.Theories.Semantics.Dynamic.Core.CCP
import Mathlib.Data.Fintype.Basic



namespace Semantics.Dynamic.Core


/--
Entities extended with the universal falsifier ⋆.

In Hofmann's system, individual drefs map to ⋆ in worlds where the
referent doesn't exist. For example, in "There's no bathroom", the
bathroom variable maps to ⋆ in all worlds.

The falsifier ⋆ satisfies: R(⋆) = false for all predicates R.
-/
inductive Entity (E : Type*) where
  | some : E → Entity E
  | star : Entity E  -- The universal falsifier ⋆
  deriving DecidableEq, Repr

namespace Entity

variable {E : Type*}

/-- Lift a predicate to handle ⋆ (false for ⋆) -/
def liftPred (p : E → Bool) : Entity E → Bool
  | .some e => p e
  | .star => false

/-- Lift a binary predicate (false if either is ⋆) -/
def liftPred₂ (p : E → E → Bool) : Entity E → Entity E → Bool
  | .some e₁, .some e₂ => p e₁ e₂
  | _, _ => false

/-- Inject regular entity -/
def inject (e : E) : Entity E := .some e

/-- Is this a real entity (not ⋆)? -/
def isSome : Entity E → Prop
  | .some _ => True
  | .star => False

instance : DecidablePred (@isSome E) := fun e => by unfold isSome; cases e <;> infer_instance

/-- Extract entity if present -/
def toOption : Entity E → Option E
  | .some e => Option.some e
  | .star => Option.none

/-- ⋆ is the universal falsifier: any lifted predicate yields false for ⋆.
    Formal statement of @cite{hofmann-2025} §2.1: "R(⋆) = 0 for all R". -/
@[simp] theorem star_falsifies (p : E → Bool) :
    Entity.liftPred p (.star : Entity E) = false := rfl

/-- ⋆ falsifies binary predicates from the left. -/
@[simp] theorem star_falsifies₂_left (p : E → E → Bool) (e : Entity E) :
    Entity.liftPred₂ p (.star : Entity E) e = false := by cases e <;> rfl

/-- ⋆ falsifies binary predicates from the right. -/
@[simp] theorem star_falsifies₂_right (p : E → E → Bool) (e : Entity E) :
    Entity.liftPred₂ p e (.star : Entity E) = false := by cases e <;> rfl

instance [Inhabited E] : Inhabited (Entity E) where
  default := .star

instance [Fintype E] : Fintype (Entity E) where
  elems := Finset.cons .star (Finset.map ⟨Entity.some, λ _ _ h => by cases h; rfl⟩ Finset.univ)
    (by simp [Finset.mem_map])
  complete := λ x => by
    cases x
    · simp [Finset.mem_map, Finset.mem_cons]
    · simp [Finset.mem_map, Finset.mem_cons]

end Entity


-- ════════════════════════════════════════════════════
-- Concept Discourse Referents
-- ════════════════════════════════════════════════════

-- Mass/Count Feature: uses `MassCount` from `Core.Lexical.Word`.

/--
A concept discourse referent value: a property annotated with a
morphosyntactic count feature.

Introduced by the NP of an antecedent DP. For example, *dog* in
*John owns a dog* introduces a concept dref anchored to the property
`λi.λx[dog(i)(x)]` with feature [COUNT].

Kind anaphors pick up concept drefs and derive kind individuals
via Chierchia's ∩ (down) operator:
- ⟦it⟧   = λP[MASS].  λi. ∩P(i)
- ⟦they⟧ = λP[COUNT]. λi. ∩(⊔P)(i)

The ⊔-closure for count nouns introduces pluralization, allowing for
the number mismatch between *a spider* (singular) and *they* (plural).
For mass nouns, ⊔-closure is vacuous (mass predicates are already
cumulative), so the singular *it* is used.
-/
structure ConceptDRef (W E : Type*) where
  /-- The property this concept is anchored to: λi.λx[P(i)(x)] -/
  property : W → E → Bool
  /-- Morphosyntactic count feature -/
  feature : MassCount

/--
Values that discourse referent indices can map to.

Standard dynamic semantics restricts assignments to map indices to
entities. @cite{krifka-2026} §4 extends this: assignments are partial
functions from ℕ to a heterogeneous universe including entities,
concepts (properties with count features), and world-time indices.

- `.entity e`: an individual referent (standard entity dref)
- `.concept c`: a concept dref — the NP property with [MASS]/[COUNT]
- `.index w`: a world-time index dref
- `.undef`: index not in the domain (models assignment partiality)

Key property: concept drefs project past operators like negation,
disjunction, and modals — they are introduced in the global
assignment, not in local sub-assignments. This is what licenses
kind anaphora out of anaphoric islands:

  *John doesn't own a dog. He is afraid of them.*

The entity dref for *a dog* is trapped under negation, but the
concept dref for 'dog' projects to the global context.
-/
inductive DRefVal (W E : Type*) where
  | entity : E → DRefVal W E
  | concept : ConceptDRef W E → DRefVal W E
  | index : W → DRefVal W E
  | undef : DRefVal W E

namespace DRefVal

variable {W E : Type*}

/-- Extract entity value, if present. -/
def getEntity : DRefVal W E → Option E
  | .entity e => some e
  | _ => none

/-- Extract concept dref, if present. -/
def getConcept : DRefVal W E → Option (ConceptDRef W E)
  | .concept c => some c
  | _ => none

/-- Extract world-time index, if present. -/
def getIndex : DRefVal W E → Option W
  | .index w => some w
  | _ => none

/-- Is this index in the domain of the assignment? -/
def isDefined : DRefVal W E → Prop
  | .undef => False
  | _ => True

instance : DecidablePred (@isDefined W E) :=
  fun d => by unfold isDefined; cases d <;> infer_instance

/-- Lift a predicate on entities to DRefVal (false for non-entities). -/
def liftEntityPred (p : E → Bool) : DRefVal W E → Bool
  | .entity e => p e
  | _ => false

/-- Lift a predicate on concepts to DRefVal (false for non-concepts). -/
def liftConceptPred (p : ConceptDRef W E → Bool) : DRefVal W E → Bool
  | .concept c => p c
  | _ => false

end DRefVal


/--
Variable indices for discourse referents.

We use natural numbers but provide type wrappers for clarity.
-/
abbrev Var := Nat

/--
A propositional variable (names a propositional dref).

Propositional variables track local contexts - the set of worlds where
an individual dref was introduced.
-/
structure PVar where
  idx : Nat
  deriving DecidableEq, Repr, Hashable

/--
An individual variable (names an individual dref).
-/
structure IVar where
  idx : Nat
  deriving DecidableEq, Repr, Hashable

/--
A concept variable (names a concept dref).

Concept variables are indices into the assignment that map to
`ConceptDRef` values — properties annotated with [MASS]/[COUNT].
-/
structure CVar where
  idx : Nat
  deriving DecidableEq, Repr, Hashable

/--
A situation variable (names a situation dref).

Parallel to `IVar` for individuals and `PVar` for propositions; like
`Var := Nat` above, kept as an `abbrev` so it inherits
`DecidableEq`/`Repr`/`Hashable`/numeric literals from `Nat`.

Used by Mendes 2025's CDRT analysis of the Subordinate Future, where
situation drefs are introduced by `SUBJ` and retrieved by `IND` across
clause boundaries (see `Theories/Semantics/{Tense,Mood}/Dynamic.lean`).
-/
abbrev SVar := Nat


/--
An ICDRT assignment maps variables to values.

In ICDRT, we need to track two kinds of assignments:
1. Individual variable assignments: IVar → Entity E
2. Propositional variable assignments: PVar → Set W

This is used by intensional dynamic semantics
(`Dynamic/Core/Intensional.lean`); simpler theories can use Nat → E.
-/
structure ICDRTAssignment (W : Type*) (E : Type*) where
  /-- Individual variable assignment: intensional individual drefs (individual
      concepts). Each variable maps worlds to entities, possibly ⋆.
      In @cite{hofmann-2025}'s notation: type s(we), i.e., for each variable v,
      v(i) is a function from worlds to entities. v(i)(w) = ⋆ when v has no
      referent in w. -/
  indiv : IVar → W → Entity E
  /-- Propositional variable assignment -/
  prop : PVar → Set W

namespace ICDRTAssignment

variable {W E : Type*}

/-- Empty assignment (all variables map to ⋆ / empty set) -/
def empty : ICDRTAssignment W E where
  indiv := λ _ _ => .star
  prop := λ _ => ∅

/-- Update individual variable with an individual concept (world-dependent). -/
def updateIndiv (g : ICDRTAssignment W E) (v : IVar) (e : W → Entity E) : ICDRTAssignment W E :=
  { g with indiv := λ v' => if v' == v then e else g.indiv v' }

/-- Update individual variable with a constant entity (world-invariant).
    Convenience for cases where the entity is the same in all worlds. -/
def updateIndivConst (g : ICDRTAssignment W E) (v : IVar) (e : Entity E) : ICDRTAssignment W E :=
  g.updateIndiv v (λ _ => e)

/-- Update propositional variable -/
def updateProp (g : ICDRTAssignment W E) (p : PVar) (s : Set W) : ICDRTAssignment W E :=
  { g with prop := λ p' => if p' == p then s else g.prop p' }

end ICDRTAssignment


/--
A propositional discourse referent: s(wt) in Hofmann's notation.

Maps each assignment to a set of worlds (the "local context" where
the associated individual dref has a referent).

In Hofmann's notation: type s(wt) = s → wt = assignment → (world → truth)

For simpler dynamic theories that don't distinguish propositional drefs,
this can be instantiated with a trivial assignment type.
-/
def PDref (W : Type*) (E : Type*) := ICDRTAssignment W E → Set W

/--
Simpler propositional dref without assignment dependence.
-/
def SimplePDref (W : Type*) := Set W

namespace PDref

variable {W E : Type*}

/-- The tautological propositional dref (all worlds) -/
def top : PDref W E := λ _ => Set.univ

/-- The contradictory propositional dref (no worlds) -/
def bot : PDref W E := λ _ => ∅

/-- Propositional dref from a classical proposition -/
def ofProp (p : W → Prop) : PDref W E := λ _ => { w | p w }

/-- Intersection of propositional drefs -/
def inter (φ ψ : PDref W E) : PDref W E := λ g => φ g ∩ ψ g

/-- Union of propositional drefs -/
def union (φ ψ : PDref W E) : PDref W E := λ g => φ g ∪ ψ g

end PDref


/--
An individual discourse referent: s(we) in Hofmann's notation.

Maps each assignment and world to an entity (possibly ⋆).

In Hofmann's notation: type s(we) = s → we = assignment → world → entity
-/
def IDref (W : Type*) (E : Type*) := ICDRTAssignment W E → W → Entity E

/--
Simpler individual dref using Nat → E assignments (for standard dynamic semantics).
-/
def SimpleIDref (W : Type*) (E : Type*) := (Nat → E) → W → E

namespace IDref

variable {W E : Type*}

/-- Constant individual dref (same entity in all contexts) -/
def const (e : Entity E) : IDref W E := λ _ _ => e

/-- The undefined individual dref (always ⋆) -/
def undef : IDref W E := λ _ _ => .star

/-- Variable lookup dref -/
def ofVar (v : IVar) : IDref W E := λ g w => g.indiv v w

/-- Apply predicate to individual dref -/
def satisfies (d : IDref W E) (p : E → W → Bool) : ICDRTAssignment W E → W → Bool :=
  λ g w => (d g w).liftPred (λ e => p e w)

end IDref


/--
A local context is a propositional dref that tracks WHERE an
individual dref was introduced.

In "Either there's no bathroom, or it's upstairs",
the bathroom is introduced in the local context of the first disjunct.
The propositional dref p_bathroom tracks: "worlds where there is a bathroom"
(the local context of the positive update).
-/
abbrev LocalContext (W : Type*) (E : Type*) := PDref W E

/--
Dynamic predication relative to a local context.

R_φ(v) is true iff R(v) holds in all worlds of the local context φ.

In Hofmann's system:
  ⟦R_φ(v)⟧^g,w = 1 iff ∀w' ∈ φ^g: R(v^g(w'))

This ensures anaphora is only felicitous when the referent exists
throughout the relevant local context.
-/
def dynamicPredication {W E : Type*}
    (R : E → W → Prop)           -- The predicate
    (φ : LocalContext W E)       -- The local context
    (v : IDref W E)              -- The individual dref
    : ICDRTAssignment W E → W → Prop :=
  λ g _ =>
    ∀ w' ∈ φ g,
      match v g w' with
      | .some e => R e w'
      | .star => False  -- ⋆ never satisfies predicates


/--
The entity domain in a local context.

DOM_e(p) = { e | e is defined throughout p }

For individual drefs that map to ⋆ in some worlds of p, those drefs
are not in the entity domain of p.
-/
def entityDomain {W E : Type*} (p : Set W) (dref : W → Entity E) : Set E :=
  { e | ∀ w ∈ p, dref w = .some e }

/--
An entity is accessible in a local context if it exists throughout.
-/
def accessibleIn {W E : Type*} (e : E) (p : Set W) (dref : W → Entity E) : Prop :=
  ∀ w ∈ p, dref w = .some e


end Semantics.Dynamic.Core
