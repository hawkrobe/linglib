import Linglib.Typology.Question
import Linglib.Phenomena.Islands.Studies.ShenHuang2026
import Linglib.Core.Lexical.ExpressiveModifier

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
- **Partial movement**: overt movement to intermediate Spec-CP, *then*
  covert movement to matrix Spec-CP — encoded as the dedicated
  `WhInterpMechanism.partialMovement` constructor (distinct from
  `.covertMovement`, which is the Huang-1982 single-step covert analysis
  used for Mandarin *daodi*).
- **Wh-in-situ**: unselective binding by Q operator in matrix C; NO
  movement (overt or covert)

The covert step in partial movement is evidenced by island sensitivity:
partial movement out of complex NPs is unacceptable (@cite{sato-ngui-2017}),
while wh-in-situ inside complex NPs is fine (as expected if no movement
crosses the island boundary).
-/

namespace Fragments.Singlish.Questions

open Typology.Question (WhInterpMechanism WhMovementStrategy)
open ShenHuang2026 (WhDependencyType)
open Core.Lexical.ExpressiveModifier
  (ExpressiveWhModifier ANDLMovementType ANDLHostPosition)

-- ============================================================================
-- Question formation strategies
-- ============================================================================

/-- A Singlish wh-question formation strategy.

    No `whReachesMatrixSpecCP` field — this is derived from the mechanism
    via `WhInterpMechanism.ReachesSpecCP`. -/
structure WhStrategy where
  /-- Human-readable label. -/
  label : String
  /-- Surface position of the wh-phrase. -/
  whPosition : WhMovementStrategy
  /-- Interpretation mechanism at the syntax-semantics interface. -/
  mechanism : WhInterpMechanism
  deriving Repr, DecidableEq

/-- Does the wh-phrase reach matrix Spec-CP? Derived from the mechanism. -/
def WhStrategy.ReachesMatrixSpecCP (s : WhStrategy) : Prop :=
  s.mechanism.ReachesSpecCP

instance (s : WhStrategy) : Decidable s.ReachesMatrixSpecCP := by
  unfold WhStrategy.ReachesMatrixSpecCP; infer_instance

/-- Full wh-movement: overt successive cyclic movement to matrix Spec-CP.
    "What you think Natalie is baking at 3am ah?" -/
def fullMovement : WhStrategy :=
  { label := "full wh-movement"
  , whPosition := .initial
  , mechanism := .overtMovement }

/-- Partial wh-movement: overt to intermediate Spec-CP, *then* covert to
    matrix Spec-CP — the dedicated two-step constructor. Distinct from
    the single-step `.covertMovement` (Huang 1982 / Mandarin *daodi*).
    "You think what Natalie is baking at 3am ah?" -/
def partialMovement : WhStrategy :=
  { label := "partial wh-movement"
  , whPosition := .mixed  -- intermediate position (not initial, not base)
  , mechanism := .partialMovement }

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

theorem fullMovement_reaches : fullMovement.ReachesMatrixSpecCP := True.intro
theorem partialMovement_reaches : partialMovement.ReachesMatrixSpecCP := True.intro
theorem whInSitu_does_not_reach : ¬ whInSitu.ReachesMatrixSpecCP := id

-- ============================================================================
-- Island sensitivity (derived from mechanism)
-- ============================================================================

/-- In-situ wh-phrases are island-insensitive (unselective binding).
    @cite{sato-ngui-2017}: (11b) vs (11a). -/
theorem inSitu_island_insensitive :
    ¬ whInSitu.mechanism.IslandSensitive := id

/-- Partially moved wh-phrases are island-sensitive — the covert second
    step crosses the boundary at LF. @cite{sato-ngui-2017}: (15). -/
theorem partial_island_sensitive :
    partialMovement.mechanism.IslandSensitive := True.intro

/-- Partial movement involves a covert step (the second of its two steps),
    distinguishing it from full overt movement. -/
theorem partial_has_covert_step :
    partialMovement.mechanism.HasCovertStep := True.intro

/-- Full movement does *not* involve a covert step. -/
theorem full_no_covert_step :
    ¬ fullMovement.mechanism.HasCovertStep := id

-- ============================================================================
-- Bridge to ShenHuang2026 WhDependencyType
-- ============================================================================

end Fragments.Singlish.Questions

/-- Map a `WhInterpMechanism` to @cite{shen-huang-2026}'s coarser
    `WhDependencyType`. Overt, covert, and partial movement all map to
    `.movement`; unselective binding maps to `.binding`. -/
def Typology.Question.WhInterpMechanism.toDependencyType :
    Typology.Question.WhInterpMechanism →
    ShenHuang2026.WhDependencyType
  | .overtMovement      => .movement
  | .covertMovement     => .movement
  | .partialMovement    => .movement
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

/-- Singlish partial movement maps to `.movement` (it has both an overt
    step and a covert step, both of which are movement operations). -/
theorem singlish_partial_is_movement :
    partialMovement.mechanism.toDependencyType = .movement := rfl

-- ============================================================================
-- The *ah* particle
-- ============================================================================

/-- *ah* is a sentence-final particle that blocks echo readings in
    wh-in-situ questions, ensuring they are interpreted as genuine
    information-seeking questions. @cite{sato-ngui-2017}: footnote 1. -/
structure SentenceFinalParticle where
  form : String
  blocksEchoReading : Bool
  deriving Repr, DecidableEq

def ah : SentenceFinalParticle :=
  { form := "ah", blocksEchoReading := true }

-- ============================================================================
-- ANDL modifier: Singlish *the-hell*
-- ============================================================================

/-- Singlish *the-hell* — an aggressively non-D-linked (ANDL) wh-modifier.
    Theory-neutral lexical entry; the Minimalist POV-feature analysis
    lives in `Theories/Syntax/Minimalism/ANDL.lean`, the empirical
    licensing data in `Phenomena/Questions/Studies/ChanShen2026.lean`.

    Parametric values: parasitic movement (must adjoin to wh-phrase;
    cannot move on its own), matrix-scope host requirement. -/
def theHell : Core.Lexical.ExpressiveModifier.ExpressiveWhModifier :=
  { form := "the hell"
  , gloss := "the-hell (ANDL intensifier)"
  , movementType := .parasitic
  , hostPosition := .matrixScope }

end Fragments.Singlish.Questions
