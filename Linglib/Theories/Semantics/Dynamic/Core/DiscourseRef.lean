/-
# Discourse Referents

Types for individual and propositional discourse referents, following
Hofmann (2025) "Anaphoric accessibility with flat update".

## Key Types

| Type | Notation | Description |
|------|----------|-------------|
| `Entity E` | e or ⋆ | Entity with universal falsifier |
| `IDref W E` | s(we) | Individual dref (assignment → world → entity) |
| `PDref W E` | s(wt) | Propositional dref (assignment → set of worlds) |

## The Universal Falsifier ⋆

In Hofmann's system, individual drefs map to ⋆ (star) in worlds where the
referent doesn't exist. For example, in "There's no bathroom", the bathroom
variable maps to ⋆ in all worlds.

The falsifier ⋆ satisfies: R(⋆) = false for all predicates R.

## Propositional Drefs as Local Contexts

ICDRT extends DRT with propositional discourse referents:
- Individual drefs: track what an expression refers to
- Propositional drefs: track where the dref was introduced (local context)

This separation enables anaphora to indefinites under negation:
"Either there's no bathroom, or it's upstairs."

## References

- Hofmann, L. (2025). Anaphoric accessibility with flat update. S&P.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
-/

import Linglib.Theories.Semantics.Dynamic.Core.Basic
import Mathlib.Data.Fintype.Basic

namespace DynamicSemantics.Core


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
def isSome : Entity E → Bool
  | .some _ => true
  | .star => false

/-- Extract entity if present -/
def toOption : Entity E → Option E
  | .some e => Option.some e
  | .star => Option.none

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
  deriving DecidableEq, BEq, Repr, Hashable

/--
An individual variable (names an individual dref).
-/
structure IVar where
  idx : Nat
  deriving DecidableEq, BEq, Repr, Hashable


/--
An ICDRT assignment maps variables to values.

In ICDRT, we need to track two kinds of assignments:
1. Individual variable assignments: IVar → Entity E
2. Propositional variable assignments: PVar → Set W

This is used by IntensionalCDRT; simpler theories can use Nat → E.
-/
structure ICDRTAssignment (W : Type*) (E : Type*) where
  /-- Individual variable assignment -/
  indiv : IVar → Entity E
  /-- Propositional variable assignment -/
  prop : PVar → Set W

namespace ICDRTAssignment

variable {W E : Type*}

/-- Empty assignment (all variables map to ⋆ / empty set) -/
def empty : ICDRTAssignment W E where
  indiv := λ _ => .star
  prop := λ _ => ∅

/-- Update individual variable -/
def updateIndiv (g : ICDRTAssignment W E) (v : IVar) (e : Entity E) : ICDRTAssignment W E :=
  { g with indiv := λ v' => if v' == v then e else g.indiv v' }

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
def ofVar (v : IVar) : IDref W E := λ g _ => g.indiv v

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


end DynamicSemantics.Core
