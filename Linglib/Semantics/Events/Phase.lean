import Mathlib.Tactic.TypeStar

/-!
# Event types as phase signatures

The modal signature of an event type: the world-conditions that must hold
*before* the event is possible (`precondition`), at its occurrence, and
*after* it (`consequence`). Originates with [roberts-simons-2024]'s account
of non-anaphoric presupposition, where ontological preconditions are what
project (`Semantics.Presupposition.Preconditions`).

Complementary decompositions elsewhere in the event API: `Event` (a
temporal *token* with runtime and sort), and
`Semantics.Aspect.SubeventStructure.TemporalDecomposition` (interval-valued
activity/result phases of a token). `EventPhase` is type-level and modal —
phases as predicates over worlds, not intervals. For change-of-state verbs
its precondition/consequence coincide with `Features.ChangeOfState`'s
presupposition/assertion pair (bridged in `Studies/RobertsSimons2024.lean`).

## Main declarations

* `EventPhase` — precondition / occurrence / consequence over worlds.
* `EventPhase.wellFormed` — occurrence entails precondition (the
  ontological constraint: you can't stop smoking unless you were smoking).
* `EventPhase.isTelic` / `EventPhase.isAtelic` — whether the consequence
  differs from the precondition (a state change) or coincides with it.
-/

variable {W : Type*}

/-- An event type decomposed into temporal phases: the state that must hold
    *before* for the event to be possible, the occurrence itself, and the
    state that holds *after*. -/
structure EventPhase (W : Type*) where
  /-- Precondition: must hold before the event for it to be possible -/
  precondition : W → Prop
  /-- The event actually occurs -/
  eventOccurs : W → Prop
  /-- Consequence: holds after the event (result state) -/
  consequence : W → Prop

namespace EventPhase

/-- Well-formed event type: the occurrence entails its precondition. -/
def wellFormed (e : EventPhase W) : Prop :=
  ∀ w, e.eventOccurs w → e.precondition w

/-- An event type is telic if its consequence differs from its precondition
    at some world (a state change). -/
def isTelic (e : EventPhase W) : Prop :=
  ∃ w, e.precondition w ≠ e.consequence w

/-- An event type is atelic if precondition and consequence coincide
    everywhere (the state persists). -/
def isAtelic (e : EventPhase W) : Prop :=
  ∀ w, e.precondition w = e.consequence w

end EventPhase
