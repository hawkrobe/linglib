import Mathlib.Order.Basic
import Linglib.Core.Time.Interval.Basic
import Linglib.Tactics.OntSort

/-!
# Neo-Davidsonian Event Semantics — type definitions

Foundational types for neo-Davidsonian event semantics
(@cite{davidson-1967}, @cite{parsons-1990}). Verbs denote predicates of
events; thematic roles are independent two-place predicates (see
`ThematicRoles.lean`).

This file is the `Defs` partner to `Basic.lean`: pure type/structure
declarations and one foundational typeclass + instance, no API. Files
that only need to *talk about* events (taking `Event Time` as an
argument, parameterizing by `[EventMereology Time]`) can import this
file alone; files that need sort predicates, dynamicity bridges, or
Davidsonian existential closure import `Basic.lean`.

## Main definitions

* `EventSort` — binary action/state ontological sort (@cite{bach-1986})
* `Event` — the unified event type: a runtime interval + sort
* `Event.τ` — temporal trace function
* `EventMereology` — part-of typeclass with τ-monotonicity + sort-preservation
* `eventPreorder` — Preorder instance derived from EventMereology
* `EvPred` / `EventPred` — predicate / world-indexed-predicate types
* `existsClosure` / `existsClosureW` — Davidsonian existential closure
* `Manner` — manner ontology (@cite{liefke-2024} §4.3)

## Naming note

`Event` is the unified type for linguistic events. The Bach 1981/1986
distinction between "eventuality" (genus, sortless) and "event" (narrow
sense, non-state) has largely collapsed in current practice —
@cite{champollion-2017} and @cite{zhao-2025} both use "event"
generically with sort/aktionsart as an inherent attribute. Tense-aspect
code that doesn't care about sort simply doesn't reference `.sort`;
sortless construction sites default to `.action`.

## References

* @cite{davidson-1967}, @cite{parsons-1990} (neo-Davidsonian foundations)
* @cite{bach-1986} (action/state ontology)
* @cite{krifka-1989} (interval-valued runtimes)
* @cite{champollion-2017}, @cite{zhao-2025} (event-as-generic)
* @cite{liefke-2024} §4.3 (manner ontology)
-/

namespace Semantics.Events

open Core.Time

/-- Binary ontological sort for events. Actions involve change; states do not. -/
inductive EventSort where
  | action  -- dynamic events (run, kick, build)
  | state   -- stative events (know, love, own)
  deriving DecidableEq, Repr, Inhabited

/-- An event: a temporal individual with ontological sort. -/
@[ont_sort] structure Event (Time : Type*) [LinearOrder Time] where
  /-- The temporal extent of this event -/
  runtime : Interval Time
  /-- Ontological sort: action or state -/
  sort : EventSort

/-- Temporal trace function τ(e) = the runtime interval of event e. -/
@[simp]
def Event.τ {Time : Type*} [LinearOrder Time] (e : Event Time) : Interval Time :=
  e.runtime

/-- A predicate over events (not world-indexed). -/
abbrev EvPred (Time : Type*) [LinearOrder Time] := Event Time → Prop

/-- A world-indexed predicate over events. The standard type for verb /
    VP denotations in tense-aspect composition. -/
abbrev EventPred (W Time : Type*) [LinearOrder Time] := W → Event Time → Prop

/-- Existential closure: ∃e. P(e). The fundamental step from event
    semantics to truth conditions. -/
def existsClosure {Time : Type*} [LinearOrder Time] (P : EvPred Time) : Prop :=
  ∃ e : Event Time, P e

/-- World-indexed existential closure: λw. ∃e. P(w)(e). -/
def existsClosureW {W Time : Type*} [LinearOrder Time]
    (P : EventPred W Time) : W → Prop :=
  λ w => ∃ e : Event Time, P w e

/-- Axioms for event part-of structure. Part-of is a partial order on
    events with temporal and sort constraints. -/
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

/-- A manner: the "how" of an event, individuated as an equivalence class
    of events under a similarity relation (@cite{liefke-2024} §4.3).
    Manners are to events what properties are to individuals. -/
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

end Semantics.Events
