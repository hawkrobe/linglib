/-
# Dynamic Semantics Shared Infrastructure

Common types for dynamic semantic theories. This module provides
the foundational structures that all dynamic semantic theories build on.

## Key Types

| Type | Description | Used By |
|------|-------------|---------|
| `Possibility W E` | (world, assignment) pair | Heim, DPL, BUS, ICDRT |
| `InfoState W E` | Set of possibilities | All theories |
| `Context W E` | InfoState + metadata | Rich dynamic theories |

## Architecture

This module provides the canonical infrastructure for dynamic semantic theories:
- `Possibility W E`: (world, assignment) pairs
- `InfoState W E`: sets of possibilities
- State relations: `subsistsIn`, `supports`

Specific theories in Theories/DynamicSemantics/ build on this:
- BUS: Elliott & Sudo 2025
- IntensionalCDRT: Hofmann 2025
- DPL: Groenendijk & Stokhof 1991
- DRT: Kamp 1981

## References

- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic. L&P 14:39-100.
-/

import Mathlib.Data.Set.Basic

namespace Theories.DynamicSemantics.Core


/--
A possibility: a world paired with a variable assignment.

This is the basic unit of information in dynamic semantics. Each possibility
represents one way the discourse could be going:
- The world component captures facts about the world
- The assignment component captures discourse referent bindings

The entity type E is the domain of individuals that variables range over.
-/
structure Possibility (W : Type*) (E : Type*) where
  /-- The possible world -/
  world : W
  /-- The variable assignment -/
  assignment : Nat → E

namespace Possibility

variable {W E : Type*}

/-- Two possibilities agree on all variables in a set -/
def agreeOn (p q : Possibility W E) (vars : Set Nat) : Prop :=
  ∀ x ∈ vars, p.assignment x = q.assignment x

/-- Same world, possibly different assignment -/
def sameWorld (p q : Possibility W E) : Prop := p.world = q.world

/-- Extend an assignment at a single variable -/
def extend (p : Possibility W E) (x : Nat) (e : E) : Possibility W E :=
  { p with assignment := fun n => if n = x then e else p.assignment n }

@[simp]
theorem extend_at (p : Possibility W E) (x : Nat) (e : E) :
    (p.extend x e).assignment x = e := by simp [extend]

@[simp]
theorem extend_other (p : Possibility W E) (x y : Nat) (e : E) (h : y ≠ x) :
    (p.extend x e).assignment y = p.assignment y := by simp [extend, h]

@[simp]
theorem extend_world (p : Possibility W E) (x : Nat) (e : E) :
    (p.extend x e).world = p.world := rfl

end Possibility


/--
An information state: a set of possibilities.

This is the fundamental type for dynamic semantics. An information state
represents the current state of the discourse - all the ways the conversation
could be going given what's been said.

Specific theories add structure:
- BUS adds bilateral structure (positive/negative)
- ICDRT adds propositional drefs
- DRT adds box structure
-/
def InfoState (W : Type*) (E : Type*) := Set (Possibility W E)

instance {W E : Type*} : Membership (Possibility W E) (InfoState W E) := Set.instMembership
instance {W E : Type*} : EmptyCollection (InfoState W E) := Set.instEmptyCollection
instance {W E : Type*} : HasSubset (InfoState W E) := Set.instHasSubset
instance {W E : Type*} : HasSSubset (InfoState W E) := Set.instHasSSubset
instance {W E : Type*} : Union (InfoState W E) := Set.instUnion
instance {W E : Type*} : Inter (InfoState W E) := Set.instInter
instance {W E : Type*} : SDiff (InfoState W E) := Set.instSDiff

@[ext]
theorem InfoState.ext {W E : Type*} {s t : InfoState W E} (h : ∀ p, p ∈ s ↔ p ∈ t) : s = t :=
  Set.ext h

namespace InfoState

variable {W E : Type*}

/-- The trivial state: all possibilities -/
def univ : InfoState W E := Set.univ

/-- The absurd state: no possibilities -/
def empty : InfoState W E := (∅ : Set (Possibility W E))

/-- State is consistent (non-empty) -/
def consistent (s : InfoState W E) : Prop := s.Nonempty

/-- State is trivial (all possibilities) -/
def trivial (s : InfoState W E) : Prop := s = Set.univ


/--
Variable x is *defined* in state s iff all possibilities agree on x's value.

This corresponds to the familiarity condition in Heim (1982): a definite
description presupposes its variable is already defined (familiar).
-/
def definedAt (s : InfoState W E) (x : Nat) : Prop :=
  ∀ p q : Possibility W E, p ∈ s → q ∈ s → p.assignment x = q.assignment x

/-- The set of defined variables in a state -/
def definedVars (s : InfoState W E) : Set Nat :=
  { x | s.definedAt x }

/--
Variable x is *novel* in state s iff x is NOT defined (free to vary).

Novel variables can be bound by existential quantifiers or indefinites.
-/
def novelAt (s : InfoState W E) (x : Nat) : Prop := ¬s.definedAt x

/-- In a consistent state, novel means assignments actually disagree -/
theorem novelAt_iff_disagree (s : InfoState W E) (x : Nat) (hs : s.consistent) :
    s.novelAt x ↔ ∃ p q : Possibility W E, p ∈ s ∧ q ∈ s ∧ p.assignment x ≠ q.assignment x := by
  constructor
  · intro h
    simp only [novelAt, definedAt] at h
    push_neg at h
    exact h
  · intro ⟨p, q, hp, hq, hne⟩
    simp only [novelAt, definedAt]
    push_neg
    exact ⟨p, q, hp, hq, hne⟩


/-- Project to the set of worlds in the state -/
def worlds (s : InfoState W E) : Set W :=
  { w | ∃ p ∈ s, p.world = w }

/-- Filter state by a world predicate -/
def filterWorlds (s : InfoState W E) (pred : W → Bool) : InfoState W E :=
  { p ∈ s | pred p.world }

/-- Filter state by an assignment predicate -/
def filterAssign (s : InfoState W E) (pred : (Nat → E) → Bool) : InfoState W E :=
  { p ∈ s | pred p.assignment }

end InfoState


/--
A context extends an information state with metadata.

This structure is useful for theories that need to track additional
information beyond the possibilities themselves, such as:
- Which variables have been introduced
- Domain restrictions for quantifiers
- Presupposition state
-/
structure Context (W : Type*) (E : Type*) where
  /-- The underlying information state -/
  state : InfoState W E
  /-- Variables that have been introduced -/
  definedVars : Set Nat := ∅
  /-- Domain of entities -/
  domain : Set E := Set.univ

namespace Context

variable {W E : Type*}

/-- Empty context with all possibilities -/
def initial : Context W E where
  state := InfoState.univ
  definedVars := ∅

/-- Context is consistent iff its state is -/
def consistent (c : Context W E) : Prop := c.state.consistent

/-- Mark a variable as defined -/
def introduce (c : Context W E) (x : Nat) : Context W E :=
  { c with definedVars := c.definedVars ∪ {x} }

/-- Narrow the state -/
def narrow (c : Context W E) (s : InfoState W E) : Context W E :=
  { c with state := c.state ∩ s }

end Context


/--
State subsistence: s subsists in s' iff every possibility in s has a
"descendant" in s'.

This notion is central to Elliott & Sudo (2025): bilateral updates must
preserve subsistence relations to validate key inferences.
-/
def InfoState.subsistsIn {W E : Type*} (s s' : InfoState W E) : Prop :=
  ∀ p ∈ s, ∃ p' ∈ s', p.world = p'.world ∧
    ∀ x, s.definedAt x → p.assignment x = p'.assignment x

notation:50 s " ⪯ " s' => InfoState.subsistsIn s s'

namespace InfoState

variable {W E : Type*}

/-- Subsistence is reflexive -/
theorem subsistsIn_refl (s : InfoState W E) : s ⪯ s := by
  intro p hp
  exact ⟨p, hp, rfl, fun _ _ => rfl⟩

/-- Subset implies subsistence -/
theorem subset_subsistsIn {s s' : InfoState W E} (h : s ⊆ s') : s ⪯ s' := by
  intro p hp
  exact ⟨p, h hp, rfl, fun _ _ => rfl⟩


/--
State s supports proposition φ iff φ holds at all worlds in s.

s ⊨ φ iff ∀p ∈ s, φ(p.world)

This is the dynamic notion of truth: a sentence is true relative to an
information state if it holds throughout that state.
-/
def supports (s : InfoState W E) (φ : W → Bool) : Prop :=
  ∀ p ∈ s, φ p.world

notation:50 s " ⊫ " φ => InfoState.supports s φ

/-- Support is preserved by subset -/
theorem supports_mono {s s' : InfoState W E} (h : s ⊆ s')
    (φ : W → Bool) (hsupp : s' ⊫ φ) : s ⊫ φ := by
  intro p hp
  exact hsupp p (h hp)

end InfoState

-- SUMMARY

/-!
## What This Module Provides

### Core Types
- `Possibility W E`: (world, assignment) pair
- `InfoState W E`: Set of possibilities
- `Context W E`: InfoState + metadata

### Possibility Operations
- `extend`: Modify assignment at one variable
- `agreeOn`: Agreement on a set of variables
- `sameWorld`: Same world component

### State Properties
- `consistent`: Non-empty state
- `definedAt`: Variable is uniquely determined
- `novelAt`: Variable is free to vary
- `definedVars`: Set of defined variables

### State Operations
- `filterWorlds`: Filter by world predicate
- `filterAssign`: Filter by assignment predicate
- `worlds`: Project to world set

### Relations
- `subsistsIn` (⪯): Every possibility has descendant
- `supports` (⊫): Proposition holds throughout state

## Architecture

This module provides shared infrastructure for:
- BUS (Bilateral Update Semantics)
- ICDRT (Intensional CDRT)
- DPL (Dynamic Predicate Logic)
- DRT (Discourse Representation Theory)

The existing `Core.HeimState` provides a similar but more specialized
infrastructure focused on Heim's File Change Semantics.
-/

end Theories.DynamicSemantics.Core
