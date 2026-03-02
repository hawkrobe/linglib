import Linglib.Theories.Semantics.Tense.TemporalConnectives.Basic
import Linglib.Theories.Semantics.Events.Basic

/-!
# Event–Interval Bridge
@cite{krifka-1989} @cite{parsons-1990}

The projection from event predicates (Level 3) to interval sets (Level 2):

```
Level 3: EvPred Time (event predicates — O&ST, future theories)
    ↓ eventDenotation (this file)
Level 2: SentDenotation Time (interval sets — Anscombe, Rett)
    ↓ timeTrace (Basic.lean)
Level 1: Set Time (point sets)
```

`eventDenotation` is the **τ-image** of an event predicate: the set of runtime
intervals of events satisfying P. It is the architectural bridge that lets
event-level theories (O&ST) be compared with interval-level theories (Rett)
and point-level theories (Anscombe).

## Key Properties

- `eventDenotation` preserves emptiness (no events ↔ empty denotation)
- Time traces factor through: `timeTrace (eventDenotation P) = { t | ∃ e, P e ∧ τ(e) contains t }`
- The projection is **sort-erasing**: event sort (action/state) is lost. This
  is correct for temporal connectives, which don't care about event sort.

-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time
open Core.Time.Interval
open Semantics.Events

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § 1: The Projection
-- ============================================================================

/-- The τ-image projection: the set of runtime intervals of events satisfying P.

    This is the fundamental bridge between event semantics (Level 3) and
    interval-set semantics (Level 2). Every event-level temporal connective
    theory can be projected down to the interval level through this map, then
    compared with Anscombe and Rett. -/
def eventDenotation (P : EvPred Time) : SentDenotation Time :=
  { i | ∃ e, P e ∧ e.τ = i }

-- ============================================================================
-- § 2: Basic Properties
-- ============================================================================

/-- Empty predicate gives empty denotation. -/
theorem eventDenotation_empty :
    eventDenotation (fun (_ : Ev Time) => False) = ∅ := by
  ext i; simp [eventDenotation]

/-- Nonempty predicate gives nonempty denotation (if there exists a witness). -/
theorem eventDenotation_nonempty (P : EvPred Time) (e : Ev Time) (he : P e) :
    e.τ ∈ eventDenotation P :=
  ⟨e, he, rfl⟩

-- ============================================================================
-- § 3: Time Trace Factoring
-- ============================================================================

/-- The time trace of an event denotation factors through τ:
    a time is in the trace iff some event satisfying P has a runtime
    containing that time.

    This is the composition `timeTrace ∘ eventDenotation`, showing that
    the full projection chain Level 3 → Level 1 can be stated directly. -/
theorem timeTrace_eventDenotation (P : EvPred Time) :
    timeTrace (eventDenotation P) = { t | ∃ e, P e ∧ e.τ.contains t } := by
  ext t
  simp only [timeTrace, eventDenotation, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, ⟨e, he, rfl⟩, hi⟩
    exact ⟨e, he, hi⟩
  · rintro ⟨e, he, hi⟩
    exact ⟨e.τ, ⟨e, he, rfl⟩, hi⟩

-- ============================================================================
-- § 4: Relationship to Canonical Denotation Patterns
-- ============================================================================

/-- A singleton event predicate (exactly one event with runtime i) gives an
    accomplishment denotation. -/
theorem eventDenotation_singleton (e₀ : Ev Time) :
    eventDenotation (fun e => e = e₀) = accomplishmentDenotation e₀.τ := by
  ext i
  simp only [eventDenotation, accomplishmentDenotation, Set.mem_setOf_eq]
  constructor
  · rintro ⟨e, rfl, rfl⟩; rfl
  · intro h; exact ⟨e₀, rfl, h.symm⟩

/-- An event predicate selecting all events with runtime subinterval of i gives
    a subset of the stative denotation.

    Note: this is a subset, not equality, because `stativeDenotation i` contains
    all subintervals including those that might not be runtimes of any event. -/
theorem eventDenotation_sub_stative (i : Interval Time) (P : EvPred Time)
    (hP : ∀ e, P e → e.τ.subinterval i) :
    eventDenotation P ⊆ stativeDenotation i := by
  intro j ⟨e, he, hj⟩
  rw [← hj]
  exact hP e he

end Semantics.Tense.TemporalConnectives
