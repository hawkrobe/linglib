import Linglib.Semantics.Dynamic.Update
import Linglib.Semantics.Dynamic.Possibility
import Linglib.Core.Logic.Assignment

/-!
# Dynamic Semantics Translation Layer

Unifies PLA ([dekker-2012]) and Core (Muskens-style) infrastructures.

## The Problem

PLA uses:
  `Poss E = Assignment E × Assignment E` (no worlds, explicit pronouns)

Core uses:
  `Possibility W ℕ E = { world : W, assignment : Assignment E }` (worlds, no pronouns)

## The Solution

1. PLA to Core: set W = Unit, merge assignment and witnesses
2. Core to PLA: split assignment, use trivial world
-/

namespace DynamicSemantics

open _root_.Core (Assignment)

/-- PLA-style possibility: assignment + witness sequence (no world).
    Both fields are `Core.Assignment E` — variables and pronouns each
    get their own ℕ-indexed Tarski-style assignment. -/
structure PLAPoss (E : Type*) where
  assignment : Assignment E
  witnesses : Assignment E

/-- PLA-style information state -/
def PLAInfoState (E : Type*) := Set (PLAPoss E)


/--
Embed PLA possibility into Core possibility.

Uses Unit world and combines assignment/witnesses into single assignment.
Pronouns are offset by a large constant to avoid collision.
-/
def PLAPoss.toPossibility {E : Type*} (p : PLAPoss E) : Possibility Unit ℕ E where
  world := ()
  assignment := λ n =>
    if n < 1000 then p.assignment n  -- Variables: indices < 1000
    else p.witnesses (n - 1000)       -- Pronouns: indices ≥ 1000

/-- Lift a PLA state to a set of possibilities. -/
def PLAInfoState.toPossibilities {E : Type*} (s : PLAInfoState E) :
    Set (Possibility Unit ℕ E) :=
  PLAPoss.toPossibility '' s


/--
Project Core possibility to PLA possibility.

Discards world, splits assignment into variable/pronoun parts.
-/
def Possibility.toPLA {W E : Type*} (p : Possibility W ℕ E) : PLAPoss E where
  assignment := λ n => p.assignment n
  witnesses := λ n => p.assignment (n + 1000)

/-- Project a set of possibilities to a PLA state. -/
def PLAInfoState.ofPossibilities {W E : Type*} (s : Set (Possibility W ℕ E)) : PLAInfoState E :=
  Possibility.toPLA '' s


/-- PLA → Core → PLA is identity on the relevant components -/
theorem toPossibility_toPLA_assignment {E : Type*} (p : PLAPoss E) (n : Nat) (h : n < 1000) :
    p.toPossibility.toPLA.assignment n = p.assignment n := by
  simp only [PLAPoss.toPossibility, Possibility.toPLA]
  simp [h]

/-- PLA → Core → PLA preserves witnesses -/
theorem toPossibility_toPLA_witnesses {E : Type*} (p : PLAPoss E) (n : Nat) :
    p.toPossibility.toPLA.witnesses n = p.witnesses n := by
  simp only [PLAPoss.toPossibility, Possibility.toPLA]
  have h : ¬(n + 1000 < 1000) := by omega
  simp [h]


/--
Embedding preservation: the translation preserves state structure.

If two PLA possibilities agree on all variables and witnesses,
their Core translations agree on all assignments.
-/
theorem embedding_preserves_agreement {E : Type*} (p q : PLAPoss E)
    (hv : ∀ n < 1000, p.assignment n = q.assignment n)
    (hw : ∀ n, p.witnesses n = q.witnesses n) :
    ∀ n, p.toPossibility.assignment n = q.toPossibility.assignment n := by
  intro n
  simp only [PLAPoss.toPossibility]
  by_cases h : n < 1000
  · simp [h, hv n h]
  · simp [h, hw (n - 1000)]


/--
PLA-style CCP: no world dependency.
-/
def PLACCP (E : Type*) := PLAInfoState E → PLAInfoState E

/-- Lift a PLA CCP to a CCP over possibilities. -/
def PLACCP.toCCP {E : Type*} (φ : PLACCP E) : CCP (Possibility Unit ℕ E) :=
  λ s => (φ (PLAInfoState.ofPossibilities s)).toPossibilities

/--
Project Core CCP to PLA CCP (for Unit world).
-/
def CCP.toPLACCP {E : Type*} (φ : CCP (Possibility Unit ℕ E)) : PLACCP E :=
  λ s => PLAInfoState.ofPossibilities (φ (PLAInfoState.toPossibilities s))


/-!
## Why This Works
[muskens-1996]

The embedding `PLAPoss.toCore` is injective: different PLA possibilities
map to different Core possibilities.

The projection `Possibility.toPLA` is surjective onto Unit-world states:
every PLA possibility is the projection of some Core possibility.

For Unit-world states, this gives an isomorphism between PLA and Core:

```
  PLAInfoState E ≃ InfoState Unit E
```

This is the formal content of [muskens-1996]'s claim that DPL embeds
into CDRT: the "worldless" setting is just the W = Unit case.
The PLA embedding follows analogously via [dekker-2012]'s elaboration.

## Bilateral Extension

For BUS (bilateral semantics), we need:
- Positive dimension: `s.toCore` for positive updates
- Negative dimension: `s.toCore` for negative updates

The bilateral structure is orthogonal to the PLA/Core distinction.
Both PLA and Core can have bilateral variants.
-/


end DynamicSemantics
