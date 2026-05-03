/-
# Neo-Davidsonian Event Semantics

Foundational event semantics following @cite{davidson-1967} and @cite{parsons-1990}.
Verbs denote predicates of events; thematic roles are independent two-place
predicates (see `ThematicRoles.lean`).

This module provides:
- Event sorts (action vs state, following @cite{bach-1986})
- The `Event` type: temporal individuals with sort
- Event mereology (part-of as partial order)
- Event predicates (`EvPred`, `EventPred`) and existential closure

## Naming note (2026 terminology)

`Event` is the unified type for linguistic events. The Bach 1981/1986
distinction between "eventuality" (genus, sortless) and "event" (narrow
sense, non-state) has largely collapsed in current practice — Champollion
2017 and Zhao 2025 both use "event" generically with sort/aktionsart as
an inherent attribute. The previous `Event Time` type (Klein/Pancheva,
runtime-only, formerly in `Tense/Aspect/Core.lean`) is now subsumed by
`Event Time`; tense-aspect code that doesn't care about sort simply
doesn't reference `.sort`. Sortless construction sites default to `.action`
with a docstring comment.

Syntax-neutral: no commitment to Voice heads or specific composition
principles. @cite{kratzer-1996} Event Identification deferred to optional
later module.

-/

import Mathlib.Order.Basic
import Linglib.Core.Time.Interval.Basic
import Linglib.Tactics.OntSort
import Linglib.Features.Aktionsart

namespace Semantics.Events

open Core.Time
open Features

-- ════════════════════════════════════════════════════
-- § 1. Event Sort (@cite{bach-1986})
-- ════════════════════════════════════════════════════

/-- Binary ontological sort for events.
    Actions involve change; states do not. -/
inductive EventSort where
  | action  -- dynamic events (run, kick, build)
  | state   -- stative events (know, love, own)
  deriving DecidableEq, Repr, Inhabited

-- ════════════════════════════════════════════════════
-- § 2. Core Event Type
-- ════════════════════════════════════════════════════

/-- An event: a temporal individual with ontological sort.
    Events have interval-valued runtimes, following @cite{krifka-1989}.

    Subsumes the historical `Event` distinction (Bach 1981/1986
    "eventuality = genus / event = narrow sense"). The field has largely
    let go of that distinction by 2026; "event" is the generic term in
    @cite{champollion-2017}, @cite{zhao-2025}, @cite{krifka-1998}. Code
    that doesn't care about sort simply doesn't reference `.sort`. -/
@[ont_sort] structure Event (Time : Type*) [LinearOrder Time] where
  /-- The temporal extent of this event -/
  runtime : Interval Time
  /-- Ontological sort: action or state -/
  sort : EventSort

/-- Temporal trace function τ(e) = the runtime interval of event e. -/
@[simp]
def Event.τ {Time : Type*} [LinearOrder Time] (e : Event Time) : Interval Time :=
  e.runtime

-- ════════════════════════════════════════════════════
-- § 3. Sort Predicates
-- ════════════════════════════════════════════════════

/-- Is this event an action (dynamic event)? -/
def Event.isAction {Time : Type*} [LinearOrder Time] (e : Event Time) : Bool :=
  e.sort == .action

/-- Is this event a state (stative event)? -/
def Event.isState {Time : Type*} [LinearOrder Time] (e : Event Time) : Bool :=
  e.sort == .state

/-- Every event is either an action or a state (exhaustivity). -/
theorem sort_exhaustive (s : EventSort) : s = .action ∨ s = .state := by
  cases s <;> simp

/-- No event is both an action and a state (exclusivity). -/
theorem sort_exclusive : EventSort.action ≠ EventSort.state := by
  decide

/-- `isAction` and `isState` are complementary. -/
theorem isAction_iff_not_isState {Time : Type*} [LinearOrder Time] (e : Event Time) :
    e.isAction = true ↔ e.isState = false := by
  simp only [Event.isAction, Event.isState]
  cases e.sort <;> decide

/-- `isState` and `isAction` are complementary. -/
theorem isState_iff_not_isAction {Time : Type*} [LinearOrder Time] (e : Event Time) :
    e.isState = true ↔ e.isAction = false := by
  simp only [Event.isAction, Event.isState]
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
    States map to.state sort; all others map to.action sort. -/
theorem vendlerClass_sort_agrees (c : VendlerClass) :
    dynamicityToEventSort c.dynamicity = match c with
      | .state => EventSort.state
      | .activity | .achievement | .accomplishment | .semelfactive => EventSort.action := by
  cases c <;> rfl

-- ════════════════════════════════════════════════════
-- § 5. Event Mereology
-- ════════════════════════════════════════════════════

/-- Axioms for event part-of structure.
    Part-of is a partial order on events with temporal and sort constraints. -/
class EventMereology (Time : Type*) [LinearOrder Time] where
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
    e₁.runtime.subinterval e₂.runtime
  /-- Sort is preserved under part-of: parts of actions are actions,
      parts of states are states -/
  sort_preserved : ∀ e₁ e₂, partOf e₁ e₂ → e₁.sort = e₂.sort

/-- Event mereology induces a Preorder. -/
instance eventPreorder (Time : Type*) [LinearOrder Time]
    [m : EventMereology Time] : Preorder (Event Time) where
  le := m.partOf
  le_refl := m.refl
  le_trans := m.trans

-- ════════════════════════════════════════════════════
-- § 6. Event Predicates (Neo-Davidsonian verb types)
-- ════════════════════════════════════════════════════

/-- A predicate over events (not world-indexed). -/
abbrev EvPred (Time : Type*) [LinearOrder Time] := Event Time → Prop

/-- A world-indexed predicate over events. The standard type for verb /
    VP denotations in tense-aspect composition. Moved here from
    `Tense/Aspect/Core.lean` (where it was the canonical predicate type
    for tense-aspect operators) as part of the event-type unification. -/
abbrev EventPred (W Time : Type*) [LinearOrder Time] := W → Event Time → Prop

/-- Existential closure: ∃e. P(e).
    The fundamental step from event semantics to truth conditions. -/
def existsClosure {Time : Type*} [LinearOrder Time] (P : EvPred Time) : Prop :=
  ∃ e : Event Time, P e

/-- World-indexed existential closure: λw. ∃e. P(w)(e). -/
def existsClosureW {W Time : Type*} [LinearOrder Time] (P : EventPred W Time) : W → Prop :=
  λ w => ∃ e : Event Time, P w e

-- ════════════════════════════════════════════════════
-- § 7. Concrete Examples (ℤ-time events)
-- ════════════════════════════════════════════════════

/-- Example: a running event from time 1 to 5. -/
def exampleRun : Event ℤ :=
  ⟨⟨1, 5, by omega⟩, .action⟩

-- ════════════════════════════════════════════════════
-- § 8. Manners (@cite{liefke-2024} §4.3)
-- ════════════════════════════════════════════════════

/-- A manner: the "how" of an event, individuated as an equivalence class
    of events under a similarity relation.

    @cite{liefke-2024}: manners are the ontological category ranged over by
    *how* in "How did John run?" and modified by manner adverbs (*quickly*,
    *carefully*). They are to events what properties are to individuals.

    Formally, a manner is a predicate on events that picks out a similarity
    class — all events sharing a characteristic quality. Two events e₁, e₂
    have the same manner w.r.t. M iff M(e₁) ∧ M(e₂).

    References:
    - Dik, S. (1975). The semantic representation of manner adverbials.
    - Alexeyenko, S. (2015). The syntax and semantics of manner modification.
    - Umbach, C. et al. (2022). Manner reference and similarity.
    - Liefke, K. (2024). Natural Language Ontology, §4.3. -/
@[ont_sort] structure Manner (Time : Type*) [LinearOrder Time] where
  /-- The characteristic predicate: which events exhibit this manner -/
  exhibits : Event Time → Prop

/-- The manner of an event under a similarity criterion.
    `mannerOf sim e` gives the manner class of `e` under `sim`. -/
def mannerOf {Time : Type*} [LinearOrder Time]
    (sim : Event Time → Event Time → Prop) (e : Event Time) : Manner Time :=
  ⟨sim e⟩

/-- Two events share a manner iff both satisfy the manner predicate. -/
def Manner.sharedBy {Time : Type*} [LinearOrder Time]
    (m : Manner Time) (e₁ e₂ : Event Time) : Prop :=
  m.exhibits e₁ ∧ m.exhibits e₂

/-- Example: a knowing state from time 0 to 10. -/
def exampleKnow : Event ℤ :=
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

end Semantics.Events
