/-
# Intensional Compositional DRT (ICDRT)

Core types for Hofmann (2025) "Anaphoric accessibility with flat update".

## Key Innovation

Hofmann's ICDRT extends DRT with **propositional discourse referents**:
- Individual drefs: s(we) - functions from assignment+world to entities
- Propositional drefs: s(wt) - functions from assignment to sets of worlds

The propositional drefs track *local contexts* - the worlds where a variable
was introduced. This enables anaphora to indefinites under negation.

## Basic Types (§2.2)

| Type | Interpretation | Hofmann Notation |
|------|----------------|------------------|
| t | Truth values | t |
| e | Entities | e |
| w | Possible worlds | w |
| s | Assignments | s |
| s(wt) | Propositional drefs | assignment → set of worlds |
| s(we) | Individual drefs | assignment → world → entity |

## References

- Hofmann, L. (2025). Anaphoric accessibility with flat update. Semantics & Pragmatics.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic. L&P 14.
- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
-/

import Linglib.Core.HeimState
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

namespace Theories.DynamicSemantics.IntensionalCDRT

open Core

-- ============================================================================
-- PART 1: Entity Domain with Universal Falsifier
-- ============================================================================

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

instance [Inhabited E] : Inhabited (Entity E) where
  default := .star

instance [Fintype E] : Fintype (Entity E) where
  elems := Finset.cons .star (Finset.map ⟨Entity.some, fun _ _ h => by cases h; rfl⟩ Finset.univ)
    (by simp [Finset.mem_map])
  complete := fun x => by
    cases x
    · simp [Finset.mem_map, Finset.mem_cons]
    · simp [Finset.mem_map, Finset.mem_cons]

end Entity

-- ============================================================================
-- PART 2: Variables (Propositional and Individual)
-- ============================================================================

/--
Variable indices for discourse referents.

We use natural numbers but distinguish propositional from individual variables
at the type level for clarity.
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

-- ============================================================================
-- PART 3: Assignments
-- ============================================================================

/--
An assignment maps variables to values.

In ICDRT, we need to track two kinds of assignments:
1. Individual variable assignments: IVar → Entity E
2. Propositional variable assignments: PVar → Set W

We represent these separately for clarity.
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
  indiv := fun _ => .star
  prop := fun _ => ∅

/-- Update individual variable -/
def updateIndiv (g : ICDRTAssignment W E) (v : IVar) (e : Entity E) : ICDRTAssignment W E :=
  { g with indiv := fun v' => if v' == v then e else g.indiv v' }

/-- Update propositional variable -/
def updateProp (g : ICDRTAssignment W E) (p : PVar) (s : Set W) : ICDRTAssignment W E :=
  { g with prop := fun p' => if p' == p then s else g.prop p' }

/-- Notation for individual variable lookup -/
notation g "⟦" v "⟧ᵢ" => ICDRTAssignment.indiv g v

/-- Notation for propositional variable lookup -/
notation g "⟦" p "⟧ₚ" => ICDRTAssignment.prop g p

end ICDRTAssignment

-- ============================================================================
-- PART 4: Discourse Referents
-- ============================================================================

/--
A propositional discourse referent: s(wt).

Maps each assignment to a set of worlds (the "local context" where
the associated individual dref has a referent).

In Hofmann's notation: type s(wt) = s → wt = assignment → (world → truth)
-/
def PDref (W : Type*) (E : Type*) := ICDRTAssignment W E → Set W

/--
An individual discourse referent: s(we).

Maps each assignment and world to an entity (possibly ⋆).

In Hofmann's notation: type s(we) = s → we = assignment → world → entity
-/
def IDref (W : Type*) (E : Type*) := ICDRTAssignment W E → W → Entity E

namespace PDref

variable {W E : Type*}

/-- The tautological propositional dref (all worlds) -/
def top : PDref W E := fun _ => Set.univ

/-- The contradictory propositional dref (no worlds) -/
def bot : PDref W E := fun _ => ∅

/-- Propositional dref from a classical proposition -/
def ofProp (p : W → Prop) : PDref W E := fun _ => { w | p w }

end PDref

namespace IDref

variable {W E : Type*}

/-- Constant individual dref (same entity in all contexts) -/
def const (e : Entity E) : IDref W E := fun _ _ => e

/-- The undefined individual dref (always ⋆) -/
def undef : IDref W E := fun _ _ => .star

end IDref

-- ============================================================================
-- PART 5: ICDRT Contexts (Information States)
-- ============================================================================

/--
An ICDRT context: a set of assignment-world pairs.

This extends Heim's file metaphor with intensional drefs. Each context
represents an information state where discourse referents have been
introduced globally (flat update) but evaluated locally.

The key insight: in flat update, ALL drefs are introduced at the top level,
but propositional drefs track WHERE (in which local context) they were
introduced. This allows anaphora under negation.
-/
def IContext (W : Type*) (E : Type*) := Set (ICDRTAssignment W E × W)

instance {W E : Type*} : Membership (ICDRTAssignment W E × W) (IContext W E) := Set.instMembership
instance {W E : Type*} : EmptyCollection (IContext W E) := Set.instEmptyCollection
instance {W E : Type*} : HasSubset (IContext W E) := Set.instHasSubset
instance {W E : Type*} : Union (IContext W E) := Set.instUnion
instance {W E : Type*} : Inter (IContext W E) := Set.instInter

namespace IContext

variable {W E : Type*}

/-- The trivial context (all possibilities) -/
def univ : IContext W E := Set.univ

/-- The absurd context (no possibilities) -/
def empty : IContext W E := ∅

/-- Context is consistent (non-empty) -/
def consistent (c : IContext W E) : Prop := c.Nonempty

/-- Worlds in the context (projection) -/
def worlds (c : IContext W E) : Set W := { w | ∃ g, (g, w) ∈ c }

/-- Update with a world-predicate -/
def update (c : IContext W E) (p : W → Prop) : IContext W E :=
  { gw ∈ c | p gw.2 }

/-- Update with an assignment-world predicate -/
def updateFull (c : IContext W E) (p : ICDRTAssignment W E → W → Prop) : IContext W E :=
  { gw ∈ c | p gw.1 gw.2 }

notation:max c "⟦" p "⟧" => IContext.update c p

end IContext

-- ============================================================================
-- PART 6: Dynamic Propositions
-- ============================================================================

/--
A dynamic proposition in ICDRT.

Maps input context to output context. This is the type of sentence
denotations in dynamic semantics.
-/
def DynProp (W : Type*) (E : Type*) := IContext W E → IContext W E

namespace DynProp

variable {W E : Type*}

/-- Identity (says nothing) -/
def id : DynProp W E := fun c => c

/-- Absurd (contradiction) -/
def absurd : DynProp W E := fun _ => ∅

/-- Tautology (accepts all) -/
def taut : DynProp W E := fun c => c

/-- Lift a classical proposition -/
def ofProp (p : W → Prop) : DynProp W E := fun c => c.update p

end DynProp

-- ============================================================================
-- PART 7: Commitment Sets
-- ============================================================================

/--
The commitment set DC_S: worlds the speaker is publicly committed to.

In Hofmann's framework, discourse consistency requires DC_S ≠ ∅.
The commitment set is computed from the speaker's assertions.

This corresponds to the common ground in Stalnaker's sense, but
tracked from the speaker's perspective.
-/
structure CommitmentSet (W : Type*) (E : Type*) where
  /-- The current context -/
  context : IContext W E
  /-- The commitment set: worlds in all surviving assignments' propositional drefs -/
  dc : Set W
  /-- Consistency: commitment set is non-empty -/
  consistent : dc.Nonempty

namespace CommitmentSet

variable {W E : Type*}

/-- Initial commitment set (all worlds) -/
def initial [Nonempty W] : CommitmentSet W E where
  context := IContext.univ
  dc := Set.univ
  consistent := Set.univ_nonempty

end CommitmentSet

-- ============================================================================
-- PART 8: Local Contexts (Propositional Drefs as Local Contexts)
-- ============================================================================

/--
A local context is a propositional dref that tracks WHERE an
individual dref was introduced.

Key insight: In "Either there's no bathroom, or it's upstairs",
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
  fun g _ =>
    ∀ w' ∈ φ g,
      match v g w' with
      | .some e => R e w'
      | .star => False  -- ⋆ never satisfies predicates

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-!
## What This Module Provides

### Entity Domain
- `Entity E`: Entities extended with universal falsifier ⋆
- `Entity.liftPred`: Lift predicates (⋆ → false)

### Variables
- `PVar`: Propositional variable indices
- `IVar`: Individual variable indices

### Assignments
- `ICDRTAssignment W E`: Combined assignment for individual and propositional drefs
- `updateIndiv`, `updateProp`: Assignment update operations

### Discourse Referents
- `PDref W E`: Propositional drefs s(wt) = assignment → set of worlds
- `IDref W E`: Individual drefs s(we) = assignment → world → entity

### Contexts
- `IContext W E`: ICDRT information states (set of assignment-world pairs)
- `DynProp W E`: Dynamic propositions (context transformers)

### Commitment
- `CommitmentSet W E`: Speaker's commitment with consistency requirement

### Local Contexts
- `LocalContext`: Alias for propositional drefs used as local contexts
- `dynamicPredication`: R_φ(v) evaluated relative to local context φ

## Architecture

This module provides the foundation. Additional modules:
- `Update.lean`: Flat update and relative variable update
- `Connectives.lean`: Negation, conjunction, disjunction, existential
- `Accessibility.lean`: Veridical/hypothetical/counterfactual classification
-/

end Theories.DynamicSemantics.IntensionalCDRT
