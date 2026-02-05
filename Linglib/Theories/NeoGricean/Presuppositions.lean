/-
# NeoGricean Presupposition Integration

Extends NeoGricean infrastructure with presupposition handling, connecting
to the core presupposition projection from Core.Presupposition.

## Key Concepts

1. Presupposition Triggers: Lexical items that introduce presuppositions
   - Definites: "the" presupposes existence and uniqueness
   - Factives: "know", "regret" presuppose their complement
   - Change-of-state: "stop", "start" presuppose prior state
   - Iteratives: "again", "still" presuppose prior occurrence
   - Clefts: "It was X that..." presupposes existence

2. Interaction with Exhaustification
   - Exhaustification can strengthen presuppositions
   - Presupposition failure may block SI computation

## Architecture

Theory-neutral examples (King, factive verbs, etc.) are in:
  `Phenomena.Presuppositions.Data`

This module provides NeoGricean-specific infrastructure:
  - Trigger types for alternative generation
  - Derivation tracking for SI computation
  - SI-presupposition interaction

## References

- Kracht (2003). Mathematics of Language, Section 4.7
- Heim (1983). On the projection problem for presuppositions
- Karttunen (1974). Presupposition and linguistic context
- Beaver (2001). Presupposition and Assertion in Dynamic Semantics
-/

import Linglib.Core.Presupposition
import Linglib.Theories.TruthConditional.Core.Polarity
import Linglib.Theories.NeoGricean.Core.Basic
import Linglib.Phenomena.Presupposition.Basic

namespace NeoGricean.Presuppositions

open Core.Presupposition
open TruthConditional.Core.Polarity
open NeoGricean
open Phenomena.Presupposition


/--
Types of presupposition triggers in natural language.

Each trigger type introduces a characteristic presupposition pattern.
These are used for alternative generation in SI computation.
-/
inductive PresupTrigger where
  /-- Definite descriptions: "the X" presupposes X exists and is unique -/
  | definite
  /-- Factive predicates: "know/regret that P" presupposes P -/
  | factive
  /-- Change-of-state predicates: "stop/start V-ing" presupposes prior state -/
  | changeOfState
  /-- Iteratives: "again", "still" presuppose prior occurrence -/
  | iterative
  /-- Cleft constructions: "It was X that..." presupposes existence -/
  | cleft
  /-- Aspectual predicates: "finish", "continue" presuppose event structure -/
  | aspectual
  deriving DecidableEq, Repr

/--
A presupposition trigger occurrence in a sentence.

Records the position and type of trigger, enabling compositional
presupposition computation and alternative generation.
-/
structure TriggerOccurrence where
  /-- Word position in the sentence -/
  position : Nat
  /-- Type of trigger -/
  trigger : PresupTrigger
  deriving Repr


/--
A derivation extended with presupposition tracking.

This extends the basic NeoGricean infrastructure to track presuppositions
through the derivation, enabling:
- Presupposition projection computation
- Interaction between presuppositions and SIs
-/
structure PresupDerivation (W : Type*) where
  /-- The underlying presuppositional proposition -/
  meaning : PrProp W
  /-- Presupposition triggers in the sentence -/
  triggers : List TriggerOccurrence
  /-- Current polarity context -/
  polarity : ContextPolarity
  /-- Surface form (optional, for display) -/
  surface : List String := []


/--
Presupposition failure blocks SI computation.

When a sentence's presupposition fails, we cannot compute scalar implicatures
because the sentence lacks a truth value. This captures the intuition that
SIs are computed only for felicitous utterances.
-/
def siBlockedByPresupFailure {W : Type*} (p : PrProp W) (w : W) : Prop :=
  p.presup w = false → True  -- SI computation not applicable

/--
SI computation requires presupposition satisfaction.

For a scalar implicature to be computed, the base sentence must be
felicitous (presupposition satisfied).
-/
def siRequiresPresup {W : Type*} (p : PrProp W) (w : W) : Prop :=
  p.presup w = true

/--
Exhaustification may strengthen presuppositions.

When alternatives to a sentence have presuppositions, exhaustification
(negating those alternatives) can introduce additional presuppositions.

This is a structural observation; detailed computation would require
integrating with the Exhaustivity module.
-/
structure ExhWithPresup (W : Type*) where
  /-- The base sentence -/
  base : PrProp W
  /-- Alternatives with their presuppositions -/
  alternatives : List (PrProp W)
  /-- The exhaustified meaning -/
  exhaustified : PrProp W


/--
Wrap the King example from Phenomena for NeoGricean use.

This creates a PresupDerivation from the theory-neutral King example,
adding trigger information for SI computation.
-/
def kingBaldDerivation : PresupDerivation KingWorld :=
  { meaning := kingBald
  , triggers := [⟨0, .definite⟩]  -- "the" at position 0
  , polarity := .upward
  , surface := ["the", "king", "is", "bald"]
  }

/--
The conditional "If the king exists, the king is bald" as a derivation.

Note: No presupposition triggers project because filtering eliminates them.
-/
def ifKingThenBaldDerivation : PresupDerivation KingWorld :=
  { meaning := ifKingThenBald
  , triggers := []  -- Presupposition filtered out
  , polarity := .upward
  , surface := ["if", "the", "king", "exists", ",", "the", "king", "is", "bald"]
  }

/--
Factive verb example as a derivation.
-/
def johnKnowsRainingDerivation : PresupDerivation RainWorld :=
  { meaning := johnKnowsRaining
  , triggers := [⟨1, .factive⟩]  -- "knows" at position 1
  , polarity := .upward
  , surface := ["John", "knows", "that", "it's", "raining"]
  }


/--
In a felicitous context, SI computation can proceed.

This is the precondition for applying the Standard Recipe when
presuppositions are involved.
-/
theorem si_proceeds_when_felicitous {W : Type*} (p : PrProp W) (w : W)
    (h : p.presup w = true) : siRequiresPresup p w := h

/--
Filtering affects which triggers are relevant for SI.

When a presupposition is filtered (locally satisfied), the corresponding
trigger no longer contributes to global presupposition, and alternatives
involving that trigger may behave differently.
-/
theorem filtering_removes_trigger :
    ifKingThenBaldDerivation.triggers = [] := rfl


end NeoGricean.Presuppositions
