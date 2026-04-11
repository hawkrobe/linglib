import Linglib.Phenomena.Questions.Typology
import Linglib.Phenomena.Islands.Studies.ShenHuang2026

/-!
# Singlish Question Formation Strategies
@cite{sato-2013} @cite{sato-ngui-2017} @cite{chan-shen-2026}

Colloquial Singapore English (Singlish) is a contact variety with an English
lexifier and Malay/southern Chinese substrate influence. It has three
interchangeable question-formation strategies for content questions
(@cite{sato-2013}):

1. **Full wh-movement**: "What you think Natalie is baking at 3am ah?"
2. **Partial wh-movement**: "You think what Natalie is baking at 3am ah?"
3. **Wh-in-situ**: "You think Natalie is baking what at 3am ah?"

All three express the same meaning ('What do you think Natalie is baking
at 3am?') and are used interchangeably. Do-support is optional in Singlish,
and *ah* is a sentence-final particle that marks wh-in-situ questions as
non-echo (@cite{sato-ngui-2017}).

## Derivational Analyses (@cite{sato-ngui-2017})

- **Full movement**: successive cyclic overt movement to matrix Spec-CP
  (same derivation as English, minus obligatory do-support)
- **Partial movement**: overt movement to intermediate Spec-CP, then
  covert movement to matrix Spec-CP
- **Wh-in-situ**: unselective binding by Q operator in matrix C; NO
  movement (overt or covert)

The covert step in partial movement is evidenced by island sensitivity:
partial movement out of complex NPs is unacceptable (@cite{sato-ngui-2017}),
while wh-in-situ inside complex NPs is fine (as expected if no movement
crosses the island boundary).
-/

namespace Fragments.Singlish.Questions

open Phenomena.Questions.Typology (WhInterpMechanism WhMovementStrategy)
open Phenomena.Islands.Studies.ShenHuang2026 (WhDependencyType)

-- ============================================================================
-- Question formation strategies
-- ============================================================================

/-- A Singlish wh-question formation strategy.

    No `whReachesMatrixSpecCP` field — this is derived from the mechanism
    via `WhInterpMechanism.reachesSpecCP`. -/
structure WhStrategy where
  /-- Human-readable label. -/
  label : String
  /-- Surface position of the wh-phrase. -/
  whPosition : WhMovementStrategy
  /-- Interpretation mechanism at the syntax-semantics interface. -/
  mechanism : WhInterpMechanism
  deriving Repr, DecidableEq

/-- Does the wh-phrase reach matrix Spec-CP? Derived from the mechanism. -/
def WhStrategy.reachesMatrixSpecCP (s : WhStrategy) : Bool :=
  s.mechanism.reachesSpecCP

/-- Full wh-movement: overt successive cyclic movement to matrix Spec-CP.
    "What you think Natalie is baking at 3am ah?" -/
def fullMovement : WhStrategy :=
  { label := "full wh-movement"
  , whPosition := .initial
  , mechanism := .overtMovement }

/-- Partial wh-movement: overt to intermediate Spec-CP, covert to matrix.
    "You think what Natalie is baking at 3am ah?" -/
def partialMovement : WhStrategy :=
  { label := "partial wh-movement"
  , whPosition := .mixed  -- intermediate position (not initial, not base)
  , mechanism := .covertMovement }

/-- Wh-in-situ: unselective binding by Q in C, no movement.
    "You think Natalie is baking what at 3am ah?" -/
def whInSitu : WhStrategy :=
  { label := "wh-in-situ"
  , whPosition := .inSitu
  , mechanism := .unselectiveBinding }

/-- All three Singlish strategies. -/
def allStrategies : List WhStrategy :=
  [fullMovement, partialMovement, whInSitu]

-- ============================================================================
-- Derived properties
-- ============================================================================

theorem fullMovement_reaches : fullMovement.reachesMatrixSpecCP = true := rfl
theorem partialMovement_reaches : partialMovement.reachesMatrixSpecCP = true := rfl
theorem whInSitu_does_not_reach : whInSitu.reachesMatrixSpecCP = false := rfl

-- ============================================================================
-- Island sensitivity (derived from mechanism)
-- ============================================================================

/-- In-situ wh-phrases are island-insensitive (unselective binding).
    @cite{sato-ngui-2017}: (11b) vs (11a). -/
theorem inSitu_island_insensitive :
    (whInSitu.mechanism).islandSensitive = false := rfl

/-- Partially moved wh-phrases are island-sensitive (covert movement
    crosses the boundary). @cite{sato-ngui-2017}: (15). -/
theorem partial_island_sensitive :
    (partialMovement.mechanism).islandSensitive = true := rfl

-- ============================================================================
-- Bridge to ShenHuang2026 WhDependencyType
-- ============================================================================

end Fragments.Singlish.Questions

/-- Map a `WhInterpMechanism` to @cite{shen-huang-2026}'s coarser
    `WhDependencyType`. Both overt and covert movement map to `.movement`;
    unselective binding maps to `.binding`. -/
def Phenomena.Questions.Typology.WhInterpMechanism.toDependencyType :
    Phenomena.Questions.Typology.WhInterpMechanism →
    Phenomena.Islands.Studies.ShenHuang2026.WhDependencyType
  | .overtMovement      => .movement
  | .covertMovement     => .movement
  | .unselectiveBinding => .binding

namespace Fragments.Singlish.Questions

/-- Singlish in-situ uses the same dependency type as Mandarin wh-in-situ:
    binding. This connects Chan & Shen's Singlish analysis to Shen &
    Huang's cross-linguistic island framework. -/
theorem singlish_insitu_is_binding :
    whInSitu.mechanism.toDependencyType = .binding := rfl

/-- Singlish full movement uses the same dependency type as English
    wh-movement: movement. -/
theorem singlish_full_is_movement :
    fullMovement.mechanism.toDependencyType = .movement := rfl

-- ============================================================================
-- The *ah* particle
-- ============================================================================

/-- *ah* is a sentence-final particle that blocks echo readings in
    wh-in-situ questions, ensuring they are interpreted as genuine
    information-seeking questions. @cite{sato-ngui-2017} -/
structure SentenceFinalParticle where
  form : String
  blocksEchoReading : Bool
  deriving Repr, DecidableEq

def ah : SentenceFinalParticle :=
  { form := "ah", blocksEchoReading := true }

end Fragments.Singlish.Questions
