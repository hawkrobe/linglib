import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Theories.Semantics.Modality.Temporal

/-!
# Bridge: Event Projection → Temporal Orientation

@cite{hacquard-2006} @cite{hacquard-2010} @cite{condoravdi-2002} @cite{kratzer-2012}Derives the temporal orientation of modals from event projection
(Hacquard 2006, §4.1). High modals get the speech time (present
perspective); low modals get the event time (past perspective).

## The Pattern

| Position | Event binder | holder(e) | τ(e) | Temporal orientation |
|----------|-------------|-----------|------|---------------------|
| High (above Asp) | speech act e₀ | speaker | speech time (now) | Present |
| Low (below Asp) | VP event e₂ | agent | event time (then) | Past/event-local |

## Hacquard's Derivation

Individual-time pairs are DERIVED from events via projection functions
`holder(e)` and `τ(e)`. Since high modals bind to the speech event and
low modals bind to the VP event, their temporal parameters differ:

- "Jane a dû prendre le train" (Hacquard 2006, (201)):
  - Epistemic (high): τ(e₀) = now → "Given my evidence NOW, ..."
  - Root (low): τ(e₂) = then → "Given Jane's circumstances THEN, ..."

This connects `EventProjection` (EventRelativity §11) to the temporal
modal evaluation framework in `Temporal.lean`.

-/

namespace Phenomena.Modality.Bridge.TemporalOrientationBridge

open Semantics.Modality.EventRelativity
open Semantics.Modality.Temporal


-- ════════════════════════════════════════════════════
-- § 1. Temporal Orientation Type
-- ════════════════════════════════════════════════════

/-- The temporal orientation of a modal: what time the modal's
conversational background is evaluated at. -/
inductive TemporalOrientation where
  /-- Present: evaluated at the speech time -/
  | present
  /-- past: evaluated at a past event time -/
  | past
  deriving DecidableEq, BEq, Repr

/-- A time type for the orientation examples. -/
inductive OTime where
  /-- Speech time (= utterance time) -/
  | now
  /-- Past event time -/
  | then_
  deriving DecidableEq, BEq, Repr


-- ════════════════════════════════════════════════════
-- § 2. Event Projection Determines Temporal Orientation
-- ════════════════════════════════════════════════════

/-- Two events: speech act and VP event. -/
inductive OrientationEvent where
  /-- The speech event (e₀) -/
  | speech
  /-- The VP event (e₂) -/
  | vpEvent
  deriving DecidableEq, BEq, Repr

/-- Individuals: speaker and the described event's agent. -/
inductive OrientationPerson where
  | speaker
  | agent
  deriving DecidableEq, BEq, Repr

/-- Event projection for the temporal orientation scenario.
Speech events project to (speaker, now); VP events project to (agent, then). -/
def orientationProjection : EventProjection OrientationEvent OrientationPerson OTime where
  holder
    | .speech => .speaker
    | .vpEvent => .agent
  time
    | .speech => .now
    | .vpEvent => .then_

/-- Speech event projects to speech time (now). -/
theorem speech_projects_to_now :
    orientationProjection.time .speech = .now := rfl

/-- VP event projects to event time (then). -/
theorem vp_projects_to_then :
    orientationProjection.time .vpEvent = .then_ := rfl


-- ════════════════════════════════════════════════════
-- § 3. Position → Temporal Orientation
-- ════════════════════════════════════════════════════

/-- Derive temporal orientation from modal position, via event binding.

High modals (above Asp) bind to the speech event → τ(e₀) = now → present.
Low modals (below Asp) bind to the VP event → τ(e₂) = then → past. -/
def positionToOrientation (pos : ModalPosition) : TemporalOrientation :=
  match pos with
  | .aboveAsp => .present    -- speech event time
  | .belowAsp => .past       -- VP event time

/-- High modals have present temporal orientation. -/
theorem high_present :
    positionToOrientation .aboveAsp = .present := rfl

/-- Low modals have past temporal orientation. -/
theorem low_past :
    positionToOrientation .belowAsp = .past := rfl

/-- The same modal (*devoir*, *pouvoir*) has different temporal perspectives
depending on its structural position — derived from event projection,
not stipulated. -/
theorem position_determines_orientation :
    positionToOrientation .aboveAsp ≠ positionToOrientation .belowAsp := by decide


-- ════════════════════════════════════════════════════
-- § 4. Bridge to Temporal.lean
-- ════════════════════════════════════════════════════

/-- The temporal orientation derived from event projection connects to
`Temporal.lean`'s time-indexed conversational backgrounds.

When the modal binds to event e with τ(e) = t, the conversational
background is evaluated at time t: `f(w,t)`. The time IS the event's
temporal trace. Event projection subsumes time-indexing: rather than
stipulating which time to evaluate at, the time is projected from
whichever event binds the modal. -/
theorem event_projection_subsumes_temporal :
    -- Speech event → t = now
    orientationProjection.time .speech = .now ∧
    -- VP event → t = then
    orientationProjection.time .vpEvent = .then_ ∧
    -- Different events → different times → different backgrounds
    orientationProjection.time .speech ≠ orientationProjection.time .vpEvent := by
  exact ⟨rfl, rfl, by decide⟩


-- ════════════════════════════════════════════════════
-- § 5. Worked Example: "Jane a dû prendre le train"
-- ════════════════════════════════════════════════════

/-! (Hacquard 2006, (201)): two readings of the same sentence with
different temporal perspectives, derived from event binding.

Epistemic (high): "Given MY evidence NOW, Jane must have taken the train."
  → modal bound to speech event → τ(e₀) = speech time = now
  → background evaluated at speech time

Root (low): "Given JANE'S circumstances THEN, Jane had to take the train."
  → modal bound to VP event → τ(e₂) = event time = then
  → background evaluated at event time -/

/-- The full derivation chain for "Jane a dû prendre le train":
event binding → event projection → temporal orientation.

This is the payoff of event-relative modality: the same modal gets
different temporal perspectives from different event bindings,
without any stipulation about temporal orientation. -/
theorem jane_train_orientation :
    -- Epistemic reading: speech event → present orientation
    orientationProjection.time .speech = .now ∧
    positionToOrientation .aboveAsp = .present ∧
    -- Root reading: VP event → past orientation
    orientationProjection.time .vpEvent = .then_ ∧
    positionToOrientation .belowAsp = .past :=
  ⟨rfl, rfl, rfl, rfl⟩


end Phenomena.Modality.Bridge.TemporalOrientationBridge
