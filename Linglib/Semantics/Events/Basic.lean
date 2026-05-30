import Linglib.Semantics.Events.Defs
import Linglib.Features.Aktionsart

/-!
# Neo-Davidsonian Event Semantics — basic API

API on top of `Events/Defs.lean`'s foundational types: sort predicates over
the `Features.Dynamicity` event sort, and concrete examples on `ℤ`-time.

Files that only need to *talk about* events should import `Defs.lean`
directly.

## Main definitions

* `Event.isAction` / `Event.isState` — decidable `Prop` sort predicates
  (the `dynamic` / `stative` poles of `Features.Dynamicity`)
* `exampleRun` / `exampleKnow` — concrete `Event ℤ` instances
-/

open Core.Time
open Features

/-! ### Sort predicates -/

/-- Is this event an action (dynamic event)? -/
def Event.isAction {Time : Type*} [LinearOrder Time] (e : Event Time) : Prop :=
  e.sort = .dynamic

/-- Is this event a state (stative event)? -/
def Event.isState {Time : Type*} [LinearOrder Time] (e : Event Time) : Prop :=
  e.sort = .stative

instance {Time : Type*} [LinearOrder Time] :
    DecidablePred (Event.isAction (Time := Time)) :=
  fun e => decEq e.sort .dynamic

instance {Time : Type*} [LinearOrder Time] :
    DecidablePred (Event.isState (Time := Time)) :=
  fun e => decEq e.sort .stative

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

/-! ### Duration predicates -/

/-- Is this event punctual (instantaneous)? Its runtime is a single point.
    The temporal-extent counterpart of the dynamicity sort; derived from the
    runtime via `Interval.IsPoint`. -/
def Event.isPunctual {Time : Type*} [LinearOrder Time] (e : Event Time) : Prop :=
  e.τ.IsPoint

/-- Is this event durative (temporally extended)? -/
def Event.isDurative {Time : Type*} [LinearOrder Time] (e : Event Time) : Prop :=
  ¬ e.isPunctual

instance {Time : Type*} [LinearOrder Time] :
    DecidablePred (Event.isPunctual (Time := Time)) :=
  fun e => by unfold Event.isPunctual Interval.IsPoint; infer_instance

instance {Time : Type*} [LinearOrder Time] :
    DecidablePred (Event.isDurative (Time := Time)) :=
  fun e => by unfold Event.isDurative; infer_instance

/-- `isDurative` and `isPunctual` are complementary. -/
theorem isDurative_iff_not_isPunctual {Time : Type*} [LinearOrder Time] (e : Event Time) :
    e.isDurative ↔ ¬ e.isPunctual := Iff.rfl

/-! ### Concrete examples (ℤ-time events) -/

/-- Example: a running event from time 1 to 5. -/
def exampleRun : Event ℤ :=
  ⟨⟨1, 5, by omega⟩, .dynamic⟩

/-- Example: a knowing state from time 0 to 10. -/
def exampleKnow : Event ℤ :=
  ⟨⟨0, 10, by omega⟩, .stative⟩

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
