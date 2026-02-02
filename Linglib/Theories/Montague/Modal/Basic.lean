/-
# Modal Theory Infrastructure

This module defines the `ModalTheory` structure for organizing competing
semantic analyses of modal auxiliaries (must, can, might, etc.).

## Competing Analyses

Modal auxiliaries have (at least) two semantic analyses:

1. **Kratzer (1977, 1981, 1991)**: Accessibility is DERIVED from conversational backgrounds
   - Modal base f: world → set of propositions (relevant facts)
   - Ordering source g: world → set of propositions (ideals for ranking)
   - Modal flavor comes from context, not lexical ambiguity

2. **Simple/Kripke (1963)**: Accessibility is PRIMITIVE
   - Direct accessibility relation R(w, w')
   - Different flavors = different relations (or different lexical items)

## Architecture

Each analysis is a `ModalTheory` instance containing:
- Core evaluation function: given modal force and proposition, compute truth at world
- Derived duality properties (□p ↔ ¬◇¬p)
- Derived consistency properties (□p → ◇p)

## References

- Kratzer, A. (1977). What 'Must' and 'Can' Must and Can Mean.
- Kratzer, A. (1981). The Notional Category of Modality.
- Kratzer, A. (1991). Modality. In Semantics: An International Handbook.
- Kripke, S. (1963). Semantical Considerations on Modal Logic.
-/

import Linglib.Theories.Montague.Verb.Attitude.Examples

namespace Montague.Modal

open Montague.Verb.Attitude.Examples

-- ============================================================================
-- Core Types
-- ============================================================================

/-- Modal force: necessity (□) or possibility (◇) -/
inductive ModalForce where
  | necessity   -- must, have to, necessarily
  | possibility -- can, may, might, possibly
  deriving DecidableEq, BEq, Repr, Inhabited

instance : ToString ModalForce where
  toString
    | .necessity => "□"
    | .possibility => "◇"

/-- A proposition is a function from worlds to truth values -/
abbrev Proposition := World → Bool

/-- The set of all worlds (from Attitudes.lean) -/
def allWorlds' : List World := allWorlds

-- ============================================================================
-- ModalTheory Structure
-- ============================================================================

/--
A semantic theory for modal auxiliaries.

Each theory specifies:
- `eval`: The core semantic content — is □p / ◇p true at world w?

## Design Note

We use a structure (not a typeclass) following mathlib conventions:
theories are passed explicitly, not resolved by instance search.
This makes theory comparisons explicit and avoids ambiguity.

## Comparison with NumeralTheory

| Aspect        | NumeralTheory               | ModalTheory                        |
|---------------|-----------------------------|------------------------------------|
| Core function | `meaning : NumWord → Nat → Bool` | `eval : ModalForce → Prop → World → Bool` |
| Utterances    | Fixed list (one, two, three)| ModalForce (necessity, possibility)|
| Worlds        | Nat (cardinalities)         | World (from Attitudes)             |
| Parameters    | None (theory IS parameters) | KratzerParams or R                 |
-/
structure ModalTheory where
  /-- Name of the theory -/
  name : String
  /-- Academic citation -/
  citation : String
  /-- Core evaluation function: is modal force applied to proposition p true at world w? -/
  eval : ModalForce → Proposition → World → Bool

-- ============================================================================
-- Derived Notions
-- ============================================================================

/--
Necessity operator: □p is true at w.
-/
def ModalTheory.necessity (T : ModalTheory) (p : Proposition) (w : World) : Bool :=
  T.eval .necessity p w

/--
Possibility operator: ◇p is true at w.
-/
def ModalTheory.possibility (T : ModalTheory) (p : Proposition) (w : World) : Bool :=
  T.eval .possibility p w

/--
Check if necessity entails possibility for this theory (consistency).

If □p holds, then ◇p should hold (assuming accessibility is serial/consistent).
This is: □p → ◇p
-/
def ModalTheory.necessityEntailsPossibility (T : ModalTheory) (p : Proposition) (w : World) : Bool :=
  !T.necessity p w || T.possibility p w

/--
Check if duality holds: □p ↔ ¬◇¬p

This is the fundamental modal duality. In terms of our Bool semantics:
- □p at w ↔ ¬(◇(¬p)) at w
-/
def ModalTheory.dualityHolds (T : ModalTheory) (p : Proposition) (w : World) : Bool :=
  let notP : Proposition := fun w' => !p w'
  let lhs := T.necessity p w
  let rhs := !T.possibility notP w
  lhs == rhs

/--
Check duality across all worlds for a proposition.
-/
def ModalTheory.checkDuality (T : ModalTheory) (p : Proposition) : Bool :=
  allWorlds'.all fun w => T.dualityHolds p w

/--
Check consistency across all worlds for a proposition.
-/
def ModalTheory.checkConsistency (T : ModalTheory) (p : Proposition) : Bool :=
  allWorlds'.all fun w => T.necessityEntailsPossibility p w

-- ============================================================================
-- Properties
-- ============================================================================

/--
A theory is normal if duality holds universally.

Normal modal logics satisfy: □p ↔ ¬◇¬p
-/
def ModalTheory.isNormal (T : ModalTheory) : Prop :=
  ∀ (p : Proposition) (w : World), T.dualityHolds p w = true

/--
A theory is consistent if necessity entails possibility universally.

This corresponds to the D axiom (seriality): □p → ◇p
-/
def ModalTheory.isConsistent (T : ModalTheory) : Prop :=
  ∀ (p : Proposition) (w : World), T.necessityEntailsPossibility p w = true

-- ============================================================================
-- Standard Test Propositions
-- ============================================================================

/-- Proposition: it is raining -/
def raining : Proposition := fun w =>
  match w with
  | .w0 => true
  | .w1 => true
  | .w2 => false
  | .w3 => false

/-- Proposition: the ground is wet -/
def groundWet : Proposition := fun w =>
  match w with
  | .w0 => true
  | .w1 => true
  | .w2 => false
  | .w3 => true

/-- Proposition: John is home -/
def johnHome : Proposition := fun w =>
  match w with
  | .w0 => true
  | .w1 => false
  | .w2 => true
  | .w3 => false

/-- A trivially true proposition (true at all worlds) -/
def triviallyTrue : Proposition := fun _ => true

/-- A trivially false proposition (false at all worlds) -/
def triviallyFalse : Proposition := fun _ => false

end Montague.Modal
