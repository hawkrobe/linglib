import Mathlib.Order.Basic
import Mathlib.Data.Set.Image
import Linglib.Core.Order.Interval
import Linglib.Features.Aktionsart

/-!
# Neo-Davidsonian Event Semantics

Foundational types and basic API for neo-Davidsonian event semantics
([davidson-1967], [parsons-1990]). Verbs denote predicates of
events; thematic roles are independent two-place predicates
(`ArgumentStructure.ThematicRel`).

## Main definitions

* `Event` — the unified event type: a runtime interval + `Features.Dynamicity` sort
* `Event.τ` — temporal trace function
* `Event.isAction` / `Event.isState` — decidable `Prop` sort predicates
  (the `dynamic` / `stative` poles of `Features.Dynamicity`)
* `Event.isPunctual` / `Event.isDurative` — decidable `Prop` duration predicates
* `Event.existsClosure` — Davidsonian existential closure
* `Event.Mereology` — part-of typeclass with τ-monotonicity + sort-preservation
* `Event.partialOrder` — `PartialOrder` instance derived from `Event.Mereology`
* `Event.Manner` — manner ontology ([liefke-2024] §4.3)
* `exampleRun` / `exampleKnow` — concrete `Event ℤ` instances

## Naming note

`Event` is the unified type for linguistic events. The Bach 1981/1986
distinction between "eventuality" (genus, sortless) and "event" (narrow
sense, non-state) has largely collapsed in current practice —
[champollion-2017] and [zhao-2025] both use "event"
generically with sort/aktionsart as an inherent attribute. Tense-aspect
code that doesn't care about sort simply doesn't reference `.sort`;
sortless construction sites default to `.dynamic`.

## References

* [davidson-1967], [parsons-1990] (neo-Davidsonian foundations)
* [bach-1986] (action/state ontology)
* [krifka-1989] (interval-valued runtimes)
* [champollion-2017], [zhao-2025] (event-as-generic)
* [liefke-2024] §4.3 (manner ontology)
-/

open Features

/-- An event: a temporal individual with ontological sort. -/
structure Event (Time : Type*) [LinearOrder Time] where
  /-- The temporal extent of this event -/
  runtime : NonemptyInterval Time
  /-- Ontological sort (aktionsart): `dynamic` or `stative` ([bach-1986]).
      This is the `Features.Dynamicity` feature — the action/state distinction
      at the event-token level. -/
  sort : Features.Dynamicity

namespace Event

variable {Time : Type*} [LinearOrder Time]

/-! ### Temporal trace -/

/-- Temporal trace function τ(e) = the runtime interval of event e. -/
@[simp]
def τ (e : Event Time) : NonemptyInterval Time :=
  e.runtime

/-! ### Sort predicates -/

/-- Is this event an action (dynamic event)? -/
def isAction (e : Event Time) : Prop :=
  e.sort = .dynamic

/-- Is this event a state (stative event)? -/
def isState (e : Event Time) : Prop :=
  e.sort = .stative

instance : DecidablePred (isAction (Time := Time)) :=
  fun e => decEq e.sort .dynamic

instance : DecidablePred (isState (Time := Time)) :=
  fun e => decEq e.sort .stative

/-- `isAction` and `isState` are complementary. -/
theorem isAction_iff_not_isState (e : Event Time) :
    e.isAction ↔ ¬ e.isState := by
  simp only [Event.isAction, Event.isState]
  cases e.sort <;> decide

/-- `isState` and `isAction` are complementary. -/
theorem isState_iff_not_isAction (e : Event Time) :
    e.isState ↔ ¬ e.isAction := by
  simp only [Event.isAction, Event.isState]
  cases e.sort <;> decide

/-! ### Duration predicates -/

/-- Is this event punctual (instantaneous)? Its runtime is a single point.
    The temporal-extent counterpart of the dynamicity sort; derived from the
    runtime via `NonemptyInterval.IsPoint`. -/
def isPunctual (e : Event Time) : Prop :=
  e.τ.IsPoint

/-- Is this event durative (temporally extended)? -/
def isDurative (e : Event Time) : Prop :=
  ¬ e.isPunctual

instance : DecidablePred (isPunctual (Time := Time)) :=
  fun e => by unfold Event.isPunctual NonemptyInterval.IsPoint; infer_instance

instance : DecidablePred (isDurative (Time := Time)) :=
  fun e => by unfold Event.isDurative; infer_instance

/-- `isDurative` and `isPunctual` are complementary. -/
theorem isDurative_iff_not_isPunctual (e : Event Time) :
    e.isDurative ↔ ¬ e.isPunctual := Iff.rfl

/-! ### Existential closure -/

/-- Existential closure: ∃e. P(e). The fundamental step from event
    semantics to truth conditions. -/
def existsClosure (P : Event Time → Prop) : Prop :=
  ∃ e : Event Time, P e

/-! ### Mereology -/

/-- Axioms for event part-of structure. Part-of is a partial order on
    events with temporal and sort constraints. -/
class Mereology (Time : Type*) [LinearOrder Time] where
  /-- e₁ is a part of e₂ -/
  partOf : Event Time → Event Time → Prop
  /-- Part-of is reflexive -/
  refl : ∀ e, partOf e e
  /-- Part-of is antisymmetric -/
  antisymm : ∀ e₁ e₂, partOf e₁ e₂ → partOf e₂ e₁ → e₁ = e₂
  /-- Part-of is transitive -/
  trans : ∀ e₁ e₂ e₃, partOf e₁ e₂ → partOf e₂ e₃ → partOf e₁ e₃
  /-- τ is monotone: if e₁ ⊑ e₂ then τ(e₁) ⊆ τ(e₂) -/
  τ_monotone : ∀ e₁ e₂, partOf e₁ e₂ →
    e₁.runtime ≤ e₂.runtime
  /-- Sort is preserved under part-of: parts of actions are actions,
      parts of states are states -/
  sort_preserved : ∀ e₁ e₂, partOf e₁ e₂ → e₁.sort = e₂.sort

/-- Event mereology induces a `PartialOrder`: parthood is reflexive,
    transitive, and antisymmetric. -/
instance partialOrder (Time : Type*) [LinearOrder Time]
    [m : Mereology Time] : PartialOrder (Event Time) where
  le := m.partOf
  le_refl := m.refl
  le_trans := m.trans
  le_antisymm := m.antisymm

/-! ### Manner -/

/-- A manner: the "how" of an event, individuated as an equivalence class
    of events under a similarity relation ([liefke-2024] §4.3).
    Manners are to events what properties are to individuals. -/
structure Manner (Time : Type*) [LinearOrder Time] where
  /-- The characteristic predicate: which events exhibit this manner -/
  exhibits : Event Time → Prop

/-- The manner of an event under a similarity criterion.
    `e.manner sim` gives the manner class of `e` under `sim`. -/
def manner (e : Event Time) (sim : Event Time → Event Time → Prop) : Manner Time :=
  ⟨sim e⟩

/-- Two events share a manner iff both satisfy the manner predicate. -/
def Manner.sharedBy (m : Manner Time) (e₁ e₂ : Event Time) : Prop :=
  m.exhibits e₁ ∧ m.exhibits e₂

end Event

/-! ### Run-time projection (event predicate → interval set)

The event→interval projection: the set of run-time intervals of the events
satisfying `P`, i.e. the image of `P` under the temporal trace τ
([krifka-1989], [krifka-1998]). This is neutral event substrate — the upper
rung of the projection ladder whose tense-specific lower rungs (`timeTrace`,
the canonical denotation patterns) live in
`Semantics/Tense/TemporalConnectives/`. It is homed here, upstream of all
aspect/tense theories, so that subinterval/homogeneity properties can be
stated as order-theoretic facts about it (see
`Semantics/Aspect/SubintervalProperty.lean`). -/

section Denotation

variable {Time : Type*} [LinearOrder Time]

/-- The event→interval projection: the set of run-time intervals of events
    satisfying `P`, i.e. the image of `P` under the temporal trace τ. Every
    event-level temporal theory projects to the interval level through this map. -/
def eventDenotation (P : Event Time → Prop) : Set (NonemptyInterval Time) :=
  Event.τ '' { e | P e }

/-- Membership in `eventDenotation`: an interval is a run-time of some `P`-event. -/
@[simp]
theorem mem_eventDenotation {P : Event Time → Prop} {i : NonemptyInterval Time} :
    i ∈ eventDenotation P ↔ ∃ e, P e ∧ e.τ = i := Iff.rfl

/-- No events satisfy `P` ↔ the denotation is empty. -/
theorem eventDenotation_eq_empty {P : Event Time → Prop} :
    eventDenotation P = ∅ ↔ ∀ e, ¬ P e := by
  rw [eventDenotation, Set.image_eq_empty]
  exact Set.eq_empty_iff_forall_notMem

/-- The run-time of any `P`-event is in the denotation. -/
theorem mem_eventDenotation_of {P : Event Time → Prop} {e : Event Time} (he : P e) :
    e.τ ∈ eventDenotation P :=
  Set.mem_image_of_mem _ he

end Denotation

/-! ### Concrete examples (ℤ-time events) -/

/-- Example: a running event from time 1 to 5. -/
def exampleRun : Event ℤ :=
  ⟨⟨⟨1, 5⟩, by omega⟩, .dynamic⟩

/-- Example: a knowing state from time 0 to 10. -/
def exampleKnow : Event ℤ :=
  ⟨⟨⟨0, 10⟩, by omega⟩, .stative⟩

/-- The run event is an action. -/
theorem exampleRun_isAction : exampleRun.isAction := rfl

/-- The know event is a state. -/
theorem exampleKnow_isState : exampleKnow.isState := rfl

/-- The run event is not a state. -/
theorem exampleRun_not_state : ¬ exampleRun.isState := by decide

/-- The know event is not an action. -/
theorem exampleKnow_not_action : ¬ exampleKnow.isAction := by decide

/-- The run event is durative. -/
theorem exampleRun_isDurative : exampleRun.isDurative := by decide

/-- The run event starts at 1. -/
theorem exampleRun_start : exampleRun.τ.fst = 1 := rfl

/-- The run event ends at 5. -/
theorem exampleRun_finish : exampleRun.τ.snd = 5 := rfl

/-- The know event spans 0 to 10. -/
theorem exampleKnow_runtime :
    exampleKnow.τ.fst = 0 ∧ exampleKnow.τ.snd = 10 :=
  ⟨rfl, rfl⟩
