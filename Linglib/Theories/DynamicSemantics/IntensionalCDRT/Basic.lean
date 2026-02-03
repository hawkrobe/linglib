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

import Linglib.Theories.DynamicSemantics.Core.Basic
import Linglib.Theories.DynamicSemantics.Core.Update
import Linglib.Theories.DynamicSemantics.Core.DiscourseRef
import Mathlib.Data.Set.Basic

namespace Theories.DynamicSemantics.IntensionalCDRT

open Theories.DynamicSemantics.Core

-- ============================================================================
-- ICDRT-specific Notation
-- ============================================================================

namespace ICDRTAssignment

variable {W E : Type*}

/-- Notation for individual variable lookup -/
notation g "⟦" v "⟧ᵢ" => ICDRTAssignment.indiv g v

/-- Notation for propositional variable lookup -/
notation g "⟦" p "⟧ₚ" => ICDRTAssignment.prop g p

end ICDRTAssignment

-- ============================================================================
-- ICDRT Contexts (Information States)
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
-- Dynamic Propositions
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
-- Commitment Sets
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
-- SUMMARY
-- ============================================================================

/-!
## What This Module Provides

### From Core.DiscourseRef (re-exported)
- `Entity E`: Entities extended with universal falsifier ⋆
- `PVar`, `IVar`: Variable indices for propositional and individual drefs
- `ICDRTAssignment W E`: Combined assignment for individual and propositional drefs
- `PDref W E`: Propositional drefs s(wt) = assignment → set of worlds
- `IDref W E`: Individual drefs s(we) = assignment → world → entity
- `LocalContext`: Alias for propositional drefs used as local contexts
- `dynamicPredication`: R_φ(v) evaluated relative to local context φ

### ICDRT-Specific
- `IContext W E`: ICDRT information states (set of assignment-world pairs)
- `DynProp W E`: Dynamic propositions (context transformers)
- `CommitmentSet W E`: Speaker's commitment with consistency requirement
- Notation: `g⟦v⟧ᵢ`, `g⟦p⟧ₚ` for variable lookup

## Architecture

This module provides the foundation. Additional modules:
- `Update.lean`: Flat update and relative variable update
- `Connectives.lean`: Negation, conjunction, disjunction, existential
- `Accessibility.lean`: Veridical/hypothetical/counterfactual classification
-/

end Theories.DynamicSemantics.IntensionalCDRT
