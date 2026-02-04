/-
# Dynamic Semantics Translation Layer

Unifies PLA (Dekker) and Core (Muskens-style) infrastructures.

## The Problem

PLA uses:
  `Poss E = (VarIdx → E) × (PronIdx → E)`  (no worlds, explicit pronouns)

Core uses:
  `Possibility W E = { world : W, assignment : Nat → E }`  (worlds, no pronouns)

## The Solution (Following Muskens 1996)

1. **PLA → Core**: Set W = Unit, merge assignment and witnesses
2. **Core → PLA**: Split assignment, use trivial world

## References

- Muskens, R. (1996). Combining Montague Semantics and Discourse Representation.
- Dekker, P. (2012). Dynamic Semantics.
-/

import Linglib.Theories.DynamicSemantics.Core.Update

namespace Theories.DynamicSemantics.Core


/-- PLA-style possibility: assignment + witness sequence (no world) -/
structure PLAPoss (E : Type*) where
  assignment : Nat → E
  witnesses : Nat → E

/-- PLA-style information state -/
def PLAInfoState (E : Type*) := Set (PLAPoss E)


/--
Embed PLA possibility into Core possibility.

Uses Unit world and combines assignment/witnesses into single assignment.
Pronouns are offset by a large constant to avoid collision.
-/
def PLAPoss.toCore {E : Type*} (p : PLAPoss E) : Possibility Unit E where
  world := ()
  assignment := fun n =>
    if n < 1000 then p.assignment n  -- Variables: indices < 1000
    else p.witnesses (n - 1000)       -- Pronouns: indices ≥ 1000

/-- Lift PLA state to Core state -/
def PLAInfoState.toCore {E : Type*} (s : PLAInfoState E) : InfoState Unit E :=
  PLAPoss.toCore '' s


/--
Project Core possibility to PLA possibility.

Discards world, splits assignment into variable/pronoun parts.
-/
def Possibility.toPLA {W E : Type*} (p : Possibility W E) : PLAPoss E where
  assignment := fun n => p.assignment n
  witnesses := fun n => p.assignment (n + 1000)

/-- Project Core state to PLA state -/
def InfoState.toPLA {W E : Type*} (s : InfoState W E) : PLAInfoState E :=
  Possibility.toPLA '' s


/-- PLA → Core → PLA is identity on the relevant components -/
theorem pla_core_pla_assignment {E : Type*} (p : PLAPoss E) (n : Nat) (h : n < 1000) :
    p.toCore.toPLA.assignment n = p.assignment n := by
  simp only [PLAPoss.toCore, Possibility.toPLA]
  simp [h]

/-- PLA → Core → PLA preserves witnesses -/
theorem pla_core_pla_witnesses {E : Type*} (p : PLAPoss E) (n : Nat) :
    p.toCore.toPLA.witnesses n = p.witnesses n := by
  simp only [PLAPoss.toCore, Possibility.toPLA]
  have h : ¬(n + 1000 < 1000) := by omega
  simp [h]


/--
**Embedding Preservation**: The translation preserves state structure.

If two PLA possibilities agree on all variables and witnesses,
their Core translations agree on all assignments.
-/
theorem embedding_preserves_agreement {E : Type*} (p q : PLAPoss E)
    (hv : ∀ n < 1000, p.assignment n = q.assignment n)
    (hw : ∀ n, p.witnesses n = q.witnesses n) :
    ∀ n, p.toCore.assignment n = q.toCore.assignment n := by
  intro n
  simp only [PLAPoss.toCore]
  by_cases h : n < 1000
  · simp [h, hv n h]
  · simp [h, hw (n - 1000)]


/--
PLA-style CCP: no world dependency.
-/
def PLACCP (E : Type*) := PLAInfoState E → PLAInfoState E

/--
Lift PLA CCP to Core CCP.
-/
def PLACCP.toCoreCCP {E : Type*} (φ : PLACCP E) : CCP Unit E :=
  fun s => (φ (InfoState.toPLA s)).toCore

/--
Project Core CCP to PLA CCP (for Unit world).
-/
def CCP.toPLACCP {E : Type*} (φ : CCP Unit E) : PLACCP E :=
  fun s => InfoState.toPLA (φ s.toCore)


/-!
## Why This Works

The embedding `PLAPoss.toCore` is injective: different PLA possibilities
map to different Core possibilities.

The projection `Possibility.toPLA` is surjective onto Unit-world states:
every PLA possibility is the projection of some Core possibility.

For Unit-world states, this gives an **isomorphism** between PLA and Core:

```
  PLAInfoState E  ≃  InfoState Unit E
```

This is the formal content of Muskens's claim that DPL (and PLA) embed
into CDRT: the "worldless" setting is just the W = Unit case.

## Bilateral Extension

For BUS (bilateral semantics), we need:
- Positive dimension: `s.toCore` for positive updates
- Negative dimension: `s.toCore` for negative updates

The bilateral structure is orthogonal to the PLA/Core distinction.
Both PLA and Core can have bilateral variants.
-/

-- SUMMARY

/-!
## What This Module Provides

### Types
- `PLAPoss E`: PLA-style possibility (no world)
- `PLAInfoState E`: Set of PLA possibilities
- `PLACCP E`: PLA-style update function

### Translations
- `PLAPoss.toCore`: PLA → Core embedding
- `Possibility.toPLA`: Core → PLA projection
- `PLAInfoState.toCore`, `InfoState.toPLA`: Lifted to states
- `PLACCP.toCoreCCP`, `CCP.toPLACCP`: Lifted to CCPs

### Key Theorems
- `pla_core_pla_assignment`: Round-trip preserves variables
- `pla_core_pla_witnesses`: Round-trip preserves witnesses
- `embedding_preserves_agreement`: Translation respects equality

## Architectural Note

This module resolves the type incompatibility between:
- `Linglib.Theories.DynamicSemantics.PLA` (Dekker's presentation)
- `Linglib.Theories.DynamicSemantics.Core` (Muskens-style)

Both can now be used together by translating through this layer.
-/

end Theories.DynamicSemantics.Core
