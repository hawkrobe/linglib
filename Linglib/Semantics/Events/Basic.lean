import Linglib.Semantics.Events.Defs
import Linglib.Features.Aktionsart

/-!
# Neo-Davidsonian Event Semantics — basic API

API on top of `Events/Defs.lean`'s foundational types: sort predicates,
EventSort ↔ Aktionsart Dynamicity bridge, concrete examples on `ℤ`-time.

Files that only need to *talk about* events should import `Defs.lean`
directly to avoid pulling in `Features.Aktionsart`.

## Main definitions

* `Event.isAction` / `Event.isState` — Bool sort predicates
* `EventSort.toDynamicity` / `dynamicityToEventSort` — Aktionsart bridge
* `vendlerClass_sort_agrees` — VendlerClass dynamicity ↔ EventSort
* `exampleRun` / `exampleKnow` — concrete `Event ℤ` instances
-/

namespace Semantics.Events

open Core.Time
open Features

/-! ### Sort predicates -/

/-- Is this event an action (dynamic event)? -/
def Event.isAction {Time : Type*} [LinearOrder Time] (e : Event Time) : Prop :=
  e.sort = .action

/-- Is this event a state (stative event)? -/
def Event.isState {Time : Type*} [LinearOrder Time] (e : Event Time) : Prop :=
  e.sort = .state

instance {Time : Type*} [LinearOrder Time] :
    DecidablePred (Event.isAction (Time := Time)) :=
  fun e => decEq e.sort .action

instance {Time : Type*} [LinearOrder Time] :
    DecidablePred (Event.isState (Time := Time)) :=
  fun e => decEq e.sort .state

/-- Every event is either an action or a state (exhaustivity). -/
theorem sort_exhaustive (s : EventSort) : s = .action ∨ s = .state := by
  cases s <;> simp

/-- No event is both an action and a state (exclusivity). -/
theorem sort_exclusive : EventSort.action ≠ EventSort.state := by
  decide

/-- `isAction` and `isState` are complementary. -/
theorem isAction_iff_not_isState {Time : Type*} [LinearOrder Time] (e : Event Time) :
    e.isAction ↔ ¬ e.isState := by
  simp only [Event.isAction, Event.isState]
  cases e.sort <;> decide

/-- `isState` and `isAction` are complementary. -/
theorem isState_iff_not_isAction {Time : Type*} [LinearOrder Time] (e : Event Time) :
    e.isState ↔ ¬ e.isAction := by
  simp only [Event.isAction, Event.isState]
  cases e.sort <;> decide

/-! ### Dynamicity Bridge (EventSort ↔ Aktionsart) -/

/-- Map EventSort to Dynamicity (the aspectual feature). -/
def EventSort.toDynamicity : EventSort → Dynamicity
  | .action => .dynamic
  | .state  => .stative

/-- Map Dynamicity back to EventSort. -/
def dynamicityToEventSort : Dynamicity → EventSort
  | .dynamic => .action
  | .stative => .state

/-- Roundtrip: toDynamicity ∘ dynamicityToEventSort = id. -/
theorem dynamicity_roundtrip (d : Dynamicity) :
    (dynamicityToEventSort d).toDynamicity = d := by
  cases d <;> rfl

/-- Roundtrip: dynamicityToEventSort ∘ toDynamicity = id. -/
theorem eventSort_roundtrip (s : EventSort) :
    dynamicityToEventSort s.toDynamicity = s := by
  cases s <;> rfl

/-- VendlerClass dynamicity agrees with EventSort classification.
    States map to .state sort; all others map to .action sort. -/
theorem vendlerClass_sort_agrees (c : VendlerClass) :
    dynamicityToEventSort c.dynamicity = match c with
      | .state => EventSort.state
      | .activity | .achievement | .accomplishment | .semelfactive => EventSort.action := by
  cases c <;> rfl

/-! ### Concrete examples (ℤ-time events) -/

/-- Example: a running event from time 1 to 5. -/
def exampleRun : Event ℤ :=
  ⟨⟨1, 5, by omega⟩, .action⟩

/-- Example: a knowing state from time 0 to 10. -/
def exampleKnow : Event ℤ :=
  ⟨⟨0, 10, by omega⟩, .state⟩

/-- The run event is an action. -/
theorem exampleRun_isAction : exampleRun.isAction := rfl

/-- The know event is a state. -/
theorem exampleKnow_isState : exampleKnow.isState := rfl

/-- The run event is not a state. -/
theorem exampleRun_not_state : ¬ exampleRun.isState := by decide

/-- The know event is not an action. -/
theorem exampleKnow_not_action : ¬ exampleKnow.isAction := by decide

/-- The run event starts at 1. -/
theorem exampleRun_start : exampleRun.τ.start = 1 := rfl

/-- The run event ends at 5. -/
theorem exampleRun_finish : exampleRun.τ.finish = 5 := rfl

/-- The know event spans 0 to 10. -/
theorem exampleKnow_runtime :
    exampleKnow.τ.start = 0 ∧ exampleKnow.τ.finish = 10 :=
  ⟨rfl, rfl⟩

end Semantics.Events
