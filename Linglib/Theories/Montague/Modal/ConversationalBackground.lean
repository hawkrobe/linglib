/-
# Conversational Backgrounds for Modal Semantics

Infrastructure for Kratzer's (1977, 1981, 1991) conversational backgrounds.

## Overview

This module provides the TYPES and BASIC OPERATIONS for conversational backgrounds.
For the full Kratzer semantics with the correct ordering relation, see `Kratzer1981.lean`.

## Key Concepts

1. **Modal Base** `f`: world → set of propositions (the relevant "facts")
2. **Ordering Source** `g`: world → set of propositions (ideals/norms for ranking)

The accessibility relation is DERIVED from the modal base:
- `R(w,w')` = w' is compatible with all propositions in f(w)

## Modal Flavors

Different conversational backgrounds yield different modal "flavors":
- **Epistemic**: f = what is known, g = ∅
- **Deontic**: f = circumstances, g = what the law requires
- **Teleological**: f = circumstances, g = goals
- **Bouletic**: f = circumstances, g = desires

## Architecture

This file provides:
- Type definitions (ModalBase, OrderingSource, etc.)
- Accessibility derived from modal base
- Simple modal operators (without ordering)
- Example conversational backgrounds

For the full Kratzer semantics with ordering, use `Kratzer1981.lean` which provides:
- Correct subset-based ordering (not counting!)
- Proven preorder properties
- Best worlds computation
- Full modal operators with ordering

## References

- Kratzer, A. (1977). What 'Must' and 'Can' Must and Can Mean.
- Kratzer, A. (1981). The Notional Category of Modality.
- Kratzer, A. (1991). Modality. In Semantics: An International Handbook.
-/

import Linglib.Theories.Montague.Verb.Attitude.Examples

namespace Montague.Modal.ConversationalBackground

open Montague.Verb.Attitude.Examples

-- ============================================================================
-- PART 1: Propositions as Sets of Worlds
-- ============================================================================

/-- A proposition is a set of worlds (equivalently, World → Bool) -/
abbrev Proposition := World → Bool

/-- The set of all worlds where a proposition holds -/
def truthSet (p : Proposition) : List World :=
  allWorlds.filter p

/-- Check if world w satisfies proposition p -/
def satisfies (w : World) (p : Proposition) : Bool := p w

/-- Check if world w satisfies ALL propositions in a set -/
def satisfiesAll (w : World) (ps : List Proposition) : Bool :=
  ps.all (satisfies w)

-- ============================================================================
-- PART 2: Conversational Backgrounds
-- ============================================================================

/--
A conversational background maps worlds to sets of propositions.

Examples:
- "What is known": maps w to the set of propositions known at w
- "What the law requires": maps w to legal requirements at w
- "What John believes": maps w to John's beliefs at w
-/
def ConversationalBackground := World → List Proposition

/--
The modal base determines which worlds are "accessible" -
those compatible with the relevant facts.
-/
abbrev ModalBase := ConversationalBackground

/--
The ordering source ranks accessible worlds by how well they
satisfy certain ideals (laws, goals, desires, etc.).

NOTE: For the correct ordering semantics (subset-based, not counting),
see `Kratzer1981.lean`.
-/
abbrev OrderingSource := ConversationalBackground

-- ============================================================================
-- PART 3: Derived Accessibility
-- ============================================================================

/--
Accessibility derived from modal base.

w' is accessible from w iff w' satisfies all propositions in f(w).
-/
def accessibleFrom (f : ModalBase) (w w' : World) : Bool :=
  satisfiesAll w' (f w)

/--
The set of worlds accessible from w given modal base f.
-/
def accessibleWorlds (f : ModalBase) (w : World) : List World :=
  allWorlds.filter (accessibleFrom f w)

-- ============================================================================
-- PART 4: Simple Modal Operators (No Ordering)
-- ============================================================================

/--
Simple necessity (no ordering): true at all accessible worlds.

This is adequate for epistemic modals where the ordering source is empty.
For modals with non-empty ordering (deontic, bouletic, etc.), use
the operators from `Kratzer1981.lean`.
-/
def mustSimple (f : ModalBase) (p : Proposition) (w : World) : Bool :=
  (accessibleWorlds f w).all p

/--
Simple possibility (no ordering): true at some accessible world.
-/
def canSimple (f : ModalBase) (p : Proposition) (w : World) : Bool :=
  (accessibleWorlds f w).any p

-- ============================================================================
-- PART 5: Modal Flavors
-- ============================================================================

/--
A modal flavor packages a modal base and ordering source.
Different flavors give different readings of the same modal verb.
-/
structure ModalFlavor where
  name : String
  base : ModalBase
  ordering : OrderingSource

-- ============================================================================
-- PART 6: Example Propositions and Backgrounds
-- ============================================================================

-- Example propositions for building conversational backgrounds
def itIsRaining : Proposition := fun w => w == .w0 || w == .w1
def johnIsHome : Proposition := fun w => w == .w0 || w == .w2
def maryIsHome : Proposition := fun w => w == .w1 || w == .w2
def theGroundIsWet : Proposition := fun w => w == .w0 || w == .w1 || w == .w3

/--
Epistemic modal base: what is known (by the speaker).
Here: we know the ground is wet.
-/
def epistemicBase : ModalBase := fun _ => [theGroundIsWet]

/--
Empty ordering source (for pure epistemic modals).
-/
def emptyOrdering : OrderingSource := fun _ => []

/--
Epistemic flavor: "It must be raining" (given we know the ground is wet)
-/
def epistemicFlavor : ModalFlavor :=
  { name := "epistemic"
  , base := epistemicBase
  , ordering := emptyOrdering
  }

/--
Circumstantial modal base: the relevant circumstances.
Here: John is home.
-/
def circumstantialBase : ModalBase := fun w =>
  if johnIsHome w then [johnIsHome] else []

/--
Deontic ordering source: what the rules require.
Here: people should stay home when it rains.
-/
def deonticOrdering : OrderingSource := fun _ => [johnIsHome, maryIsHome]

/--
Deontic flavor: "John must stay home" (given the rules)
-/
def deonticFlavor : ModalFlavor :=
  { name := "deontic"
  , base := circumstantialBase
  , ordering := deonticOrdering
  }

-- ============================================================================
-- PART 7: Examples with Simple Modals
-- ============================================================================

-- Epistemic "must" (simple): given the ground is wet, must it be raining?
-- Accessible worlds (where ground is wet): {w0, w1, w3}
-- Worlds where it's raining: {w0, w1}
-- Is it raining at ALL accessible worlds? No (w3 is accessible but not raining)
#eval mustSimple epistemicBase itIsRaining .w0  -- false

-- Epistemic "can" (simple): given the ground is wet, can it be raining?
#eval canSimple epistemicBase itIsRaining .w0  -- true

-- If we know MORE (restrict the modal base), necessity becomes easier to satisfy.
def strongerEpistemicBase : ModalBase := fun _ => [theGroundIsWet, itIsRaining]

#eval mustSimple strongerEpistemicBase itIsRaining .w0  -- true

/--
**Theorem: Stronger knowledge → easier necessity**

Adding propositions to modal base restricts accessible worlds,
making necessity easier to achieve.
-/
theorem stronger_base_easier_necessity :
    -- With weak base, "must rain" is false
    mustSimple epistemicBase itIsRaining .w0 = false ∧
    -- With stronger base, "must rain" is true
    mustSimple strongerEpistemicBase itIsRaining .w0 = true := by
  native_decide

-- ============================================================================
-- PART 8: Connection to Kratzer1981
-- ============================================================================

/-!
## Full Kratzer Semantics

For modals with non-empty ordering sources (deontic, bouletic, teleological),
use `Kratzer1981.lean` which provides:

- `atLeastAsGoodAs`: Correct subset-based ordering (Kratzer p. 39)
- `bestWorlds`: Worlds not dominated by better worlds
- `necessity`, `possibility`: Full modal operators with ordering
- Proven properties: reflexivity, transitivity, duality, K axiom

The simple operators here (`mustSimple`, `canSimple`) are equivalent to
Kratzer semantics with empty ordering source.
-/

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Core Types
- `Proposition`: World → Bool
- `ConversationalBackground`: World → List Proposition
- `ModalBase`: Facts that determine accessibility
- `OrderingSource`: Ideals that rank accessible worlds
- `ModalFlavor`: Packaged modal base + ordering

### Derived Notions
- `accessibleFrom`: Derived accessibility relation
- `accessibleWorlds`: Set of accessible worlds

### Simple Modal Operators (no ordering)
- `mustSimple`: Universal quantification over accessible worlds
- `canSimple`: Existential quantification over accessible worlds

### Example Backgrounds
- `epistemicBase`: Knowledge that ground is wet
- `circumstantialBase`: Circumstances (John is home)
- `deonticOrdering`: Norms (people should stay home)
- `epistemicFlavor`, `deonticFlavor`: Packaged flavors

### For Full Kratzer Semantics
See `Kratzer1981.lean` for:
- Correct ordering relation (subset-based)
- Best worlds with ordering
- Full modal operators
- Proven correspondence theorems
-/

end Montague.Modal.ConversationalBackground
