/-
# Neo-Davidsonian Event Semantics

Foundational event semantics following Davidson (1967) and Parsons (1990).
Verbs denote predicates of events; thematic roles are independent two-place
predicates (see `ThematicRoles.lean`).

This module provides:
- Event sorts (action vs state, following Bach 1986)
- The `Ev` type: temporal individuals with sort
- Bridges to `Verb.Aspect.Dynamicity` and `ViewpointAspect.Eventuality`
- Event mereology (part-of as partial order)
- Event predicates (`EvPred`, `EvPredW`) and existential closure

Syntax-neutral: no commitment to Voice heads or specific composition
principles. Kratzer (1996) Event Identification deferred to optional
later module.

## References

- Davidson, D. (1967). The logical form of action sentences.
- Parsons, T. (1990). Events in the Semantics of English.
- Bach, E. (1986). The algebra of events.
- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics.
-/

import Mathlib.Order.Basic
import Linglib.Theories.TruthConditional.Core.Time
import Linglib.Theories.TruthConditional.Verb.Aspect
import Linglib.Theories.TruthConditional.Verb.ViewpointAspect

namespace EventSemantics

open TruthConditional.Core.Time
open TruthConditional.Verb.Aspect
open TruthConditional.Verb.ViewpointAspect

-- ════════════════════════════════════════════════════
-- § 1. Event Sort (Bach 1986)
-- ════════════════════════════════════════════════════

/-- Binary ontological sort for eventualities (Bach 1986).
    Actions involve change; states do not. -/
inductive EventSort where
  | action  -- dynamic eventualities (run, kick, build)
  | state   -- stative eventualities (know, love, own)
  deriving DecidableEq, Repr, BEq, Inhabited

-- ════════════════════════════════════════════════════
-- § 2. Core Event Type
-- ════════════════════════════════════════════════════

/-- An event: a temporal individual with ontological sort (Parsons 1990).
    Events have interval-valued runtimes, following Krifka (1989). -/
structure Ev (Time : Type*) [LE Time] where
  /-- The temporal extent of this event -/
  runtime : Interval Time
  /-- Ontological sort: action or state -/
  sort : EventSort

/-- Temporal trace function τ(e) = the runtime interval of event e. -/
@[simp]
def Ev.τ {Time : Type*} [LE Time] (e : Ev Time) : Interval Time :=
  e.runtime

-- ════════════════════════════════════════════════════
-- § 3. Sort Predicates
-- ════════════════════════════════════════════════════

/-- Is this event an action (dynamic eventuality)? -/
def Ev.isAction {Time : Type*} [LE Time] (e : Ev Time) : Bool :=
  e.sort == .action

/-- Is this event a state (stative eventuality)? -/
def Ev.isState {Time : Type*} [LE Time] (e : Ev Time) : Bool :=
  e.sort == .state

/-- Every event is either an action or a state (exhaustivity). -/
theorem sort_exhaustive (s : EventSort) : s = .action ∨ s = .state := by
  cases s <;> simp

/-- No event is both an action and a state (exclusivity). -/
theorem sort_exclusive : EventSort.action ≠ EventSort.state := by
  decide

/-- `isAction` and `isState` are complementary. -/
theorem isAction_iff_not_isState {Time : Type*} [LE Time] (e : Ev Time) :
    e.isAction = true ↔ e.isState = false := by
  simp only [Ev.isAction, Ev.isState]
  cases e.sort <;> decide

/-- `isState` and `isAction` are complementary. -/
theorem isState_iff_not_isAction {Time : Type*} [LE Time] (e : Ev Time) :
    e.isState = true ↔ e.isAction = false := by
  simp only [Ev.isAction, Ev.isState]
  cases e.sort <;> decide

-- ════════════════════════════════════════════════════
-- § 4. Dynamicity Bridge (EventSort ↔ VendlerClass.dynamicity)
-- ════════════════════════════════════════════════════

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
      | .activity | .achievement | .accomplishment => EventSort.action := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════
-- § 5. Eventuality Bridge (Ev ↔ ViewpointAspect.Eventuality)
-- ════════════════════════════════════════════════════

/-- Forget the sort: project Ev down to Eventuality. -/
def Ev.toEventuality {Time : Type*} [LE Time] (e : Ev Time) : Eventuality Time :=
  ⟨e.runtime⟩

/-- Lift an Eventuality to Ev with a given sort. -/
def eventualityToEv {Time : Type*} [LE Time]
    (ev : Eventuality Time) (s : EventSort) : Ev Time :=
  ⟨ev.runtime, s⟩

/-- Roundtrip: toEventuality ∘ eventualityToEv forgets the sort
    (we recover the Eventuality). -/
theorem toEv_toEventuality_roundtrip {Time : Type*} [LE Time]
    (ev : Eventuality Time) (s : EventSort) :
    (eventualityToEv ev s).toEventuality = ev := by
  cases ev; rfl

/-- The temporal trace is preserved by the Ev → Eventuality projection. -/
theorem toEventuality_τ {Time : Type*} [LE Time] (e : Ev Time) :
    e.toEventuality.τ = e.τ := by
  cases e; rfl

/-- Lift an EventPred (over Eventuality) to a world-indexed predicate over Ev,
    ignoring the sort. -/
def EventPred.liftToEv {W Time : Type*} [LE Time]
    (P : EventPred W Time) : W → Ev Time → Prop :=
  λ w e => P w e.toEventuality

-- ════════════════════════════════════════════════════
-- § 6. Event Mereology
-- ════════════════════════════════════════════════════

/-- Axioms for event part-of structure (Bach 1986, Krifka 1989).
    Part-of is a partial order on events with temporal and sort constraints. -/
class EventMereology (Time : Type*) [LinearOrder Time] where
  /-- e₁ is a part of e₂ -/
  partOf : Ev Time → Ev Time → Prop
  /-- Part-of is reflexive -/
  refl : ∀ e, partOf e e
  /-- Part-of is antisymmetric -/
  antisymm : ∀ e₁ e₂, partOf e₁ e₂ → partOf e₂ e₁ → e₁ = e₂
  /-- Part-of is transitive -/
  trans : ∀ e₁ e₂ e₃, partOf e₁ e₂ → partOf e₂ e₃ → partOf e₁ e₃
  /-- τ is monotone: if e₁ ⊑ e₂ then τ(e₁) ⊆ τ(e₂) -/
  τ_monotone : ∀ e₁ e₂, partOf e₁ e₂ →
    e₁.runtime.subinterval e₂.runtime
  /-- Sort is preserved under part-of: parts of actions are actions,
      parts of states are states -/
  sort_preserved : ∀ e₁ e₂, partOf e₁ e₂ → e₁.sort = e₂.sort

/-- Event mereology induces a Preorder. -/
instance eventPreorder (Time : Type*) [LinearOrder Time]
    [m : EventMereology Time] : Preorder (Ev Time) where
  le := m.partOf
  le_refl := m.refl
  le_trans := m.trans

-- ════════════════════════════════════════════════════
-- § 7. Event Predicates (Neo-Davidsonian verb types)
-- ════════════════════════════════════════════════════

/-- A predicate over events (not world-indexed). -/
abbrev EvPred (Time : Type*) [LE Time] := Ev Time → Prop

/-- A world-indexed predicate over events. -/
abbrev EvPredW (W Time : Type*) [LE Time] := W → Ev Time → Prop

/-- Existential closure: ∃e. P(e).
    The fundamental step from event semantics to truth conditions. -/
def existsClosure {Time : Type*} [LE Time] (P : EvPred Time) : Prop :=
  ∃ e : Ev Time, P e

/-- World-indexed existential closure: λw. ∃e. P(w)(e). -/
def existsClosureW {W Time : Type*} [LE Time] (P : EvPredW W Time) : W → Prop :=
  λ w => ∃ e : Ev Time, P w e

-- ════════════════════════════════════════════════════
-- § 8. Concrete Examples (ℤ-time events)
-- ════════════════════════════════════════════════════

/-- Example: a running event from time 1 to 5. -/
def exampleRun : Ev ℤ :=
  ⟨⟨1, 5, by omega⟩, .action⟩

/-- Example: a knowing state from time 0 to 10. -/
def exampleKnow : Ev ℤ :=
  ⟨⟨0, 10, by omega⟩, .state⟩

/-- The run event is an action. -/
theorem exampleRun_isAction : exampleRun.isAction = true := rfl

/-- The know event is a state. -/
theorem exampleKnow_isState : exampleKnow.isState = true := rfl

/-- The run event is not a state. -/
theorem exampleRun_not_state : exampleRun.isState = false := rfl

/-- The know event is not an action. -/
theorem exampleKnow_not_action : exampleKnow.isAction = false := rfl

/-- The run event starts at 1. -/
theorem exampleRun_start : exampleRun.τ.start = 1 := rfl

/-- The run event ends at 5. -/
theorem exampleRun_finish : exampleRun.τ.finish = 5 := rfl

/-- The know event spans 0 to 10. -/
theorem exampleKnow_runtime :
    exampleKnow.τ.start = 0 ∧ exampleKnow.τ.finish = 10 :=
  ⟨rfl, rfl⟩

/-- Projecting the run event to Eventuality preserves the runtime. -/
theorem exampleRun_toEventuality_τ :
    exampleRun.toEventuality.τ = exampleRun.τ :=
  toEventuality_τ exampleRun

end EventSemantics
