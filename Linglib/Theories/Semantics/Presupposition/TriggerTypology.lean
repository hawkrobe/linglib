import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Entailment.Polarity

/-!
# Presupposition Trigger Typology
@cite{wang-2025}

Cross-linguistic typology of presupposition triggers, classifying triggers
by what non-presuppositional alternative they have. The classification
follows @cite{wang-2025} Table 4.1 and is consumed by:

- `Phenomena/Presupposition/Studies/Wang2025.lean` — IC ≫ FP ≫ MP
  constraint-based competition analysis
- `Fragments/Mandarin/Particles.lean` — Mandarin trigger entries

## Classification

Three patterns of trigger ↔ alternative relationship:
1. **Deletion alternatives** — trigger can be deleted (ye/also → ∅)
2. **Replacement alternatives** — specific lexical replacement (zhidao/know → believe)
3. **No structural alternative** — no available alternative (jiu/only)

The alternative-structure axis predicts obligatoriness:
- Deletion / replacement → trigger can be optional or obligatory
- No alternative → trigger is mandatorily omitted under partial CG support

## Relation to MP infrastructure

This file provides the **typology**; the constraint-based formulation of
Maximize Presupposition lives in `MaximizePresupposition.lean`, and the
paper-specific IC/FP/MP ranking in `Phenomena/Presupposition/Studies/Wang2025.lean`.
-/

namespace Semantics.Presupposition.TriggerTypology

open Core.Presupposition
open Semantics.Entailment.Polarity

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

Tracks presuppositions through the derivation, enabling:
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


-- ============================================================================
-- @cite{wang-2025} Table 4.1: Alternative-structure typology
-- ============================================================================

/--
@cite{wang-2025} Table 4.1: How a presupposition trigger relates to its
non-presuppositional alternative.
-/
inductive AltStructure where
  /-- Alternative is obtained by deleting the trigger (ye/also → ∅, you/again → ∅) -/
  | deletion
  /-- Alternative is a specific lexical replacement (zhidao/know → believe) -/
  | replacement
  /-- No structural alternative available (jiu/only) -/
  | none
  deriving DecidableEq, Repr

/--
Obligatoriness pattern predicted by the alternative-structure typology.

@cite{wang-2025} derives three patterns from the interaction of trigger
type, alternative structure, and constraint ranking:
1. Obligatory: trigger must be used when CG supports presupposition
2. Optional: trigger may or may not be used
3. Blocked: trigger must NOT be used (mandatorily omitted)
-/
inductive Obligatoriness where
  /-- Trigger is obligatory when presupposition is fully entailed by CG -/
  | obligatory
  /-- Trigger is optional (either form is acceptable) -/
  | optional
  /-- Trigger is blocked (mandatorily omitted in this context) -/
  | blocked
  deriving DecidableEq, Repr

/--
A presupposition trigger entry with @cite{wang-2025} alternative structure.

Extends the basic trigger type with information about what non-presuppositional
alternative exists, enabling the constraint-based competition analysis.
-/
structure PresupTriggerEntry where
  /-- The trigger type (from existing classification) -/
  trigger : PresupTrigger
  /-- Alternative structure (Wang Table 4.1) -/
  altStructure : AltStructure
  /-- Lexical form of the alternative (if replacement) -/
  altForm : Option String := .none
  deriving Repr

/--
Assign alternative structure to standard trigger types.

Default mapping based on cross-linguistic generalizations.
Language-specific entries may override (see Fragments/Mandarin/).
-/
def PresupTrigger.defaultAltStructure : PresupTrigger → AltStructure
  | .definite => .replacement    -- "the" → "a"
  | .factive => .replacement     -- "know" → "believe"
  | .changeOfState => .replacement -- "stop" → "not do"
  | .iterative => .deletion      -- "again" → ∅
  | .cleft => .none              -- no obvious alternative
  | .aspectual => .replacement   -- "start" → "do"

end Semantics.Presupposition.TriggerTypology
