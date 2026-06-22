/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Tense.TemporalConnectives.Basic
import Linglib.Semantics.Events.Basic

/-!
# The event→interval projection
[krifka-1989] [krifka-1998] [parsons-1990] [champollion-2017]

`eventDenotation` projects a (neo-Davidsonian, [parsons-1990]) event predicate to the
set of run-time intervals of its events: the image of the predicate under the temporal
trace τ ([krifka-1989], [krifka-1998]). It is the upper rung of the three-level
projection ladder whose lower rungs (`timeTrace`, the denotation patterns) live in
`Basic.lean`:

```
Level 3: Event Time → Prop   (event predicates — O&ST, future theories)
    ↓ eventDenotation (this file)
Level 2: SentDenotation Time (interval sets — Anscombe, Rett)
    ↓ timeTrace (Basic.lean)
Level 1: Set Time            (point sets)
```

Concretely `eventDenotation P = Event.τ '' { e | P e }`, so its basic properties are
mathlib's `Set.image` API specialised to τ; `mem_eventDenotation` is the membership
characterisation consumers rewrite with.

## Scope of the abstraction

The projection factors only through `e.τ`, **discarding `e.sort`** (action/state) and
all non-temporal event structure — mereology, causation, thematic roles. The
sum-homomorphism content of τ ([krifka-1998], [champollion-2017]) developed in
`Semantics/Events/CEM.lean` is likewise not used here; this is the plain set-image.

Two caveats the framing must own:

- **Sort is dropped by choice, not because connectives ignore aktionsart.** They do
  not: `while` selects atelic eventualities, and `when`'s overlap-vs-sequence reading
  is telicity-driven. The abstraction is appropriate for the interval-level comparison
  targets (O&ST, Rett, Anscombe), which are stated over run-times; a sort-sensitive
  connective would retain `e.sort` and fall outside this projection.
- **Run-time is identified with the located interval, so the chain is aspect-neutral.**
  τ(e) is the event's own extent; the interval a tense/aspect operator locates is the
  reference time, and the run-time ≠ reference-time gap *is* grammatical aspect
  (perfective: reference ⊇ run-time; imperfective: ⊆). This bridge is the
  perfective-default identification of the two.

## Related projections

`Semantics/Aspect/Basic.lean` carries a parallel, world-indexed family (`IntervalPred`,
with `PRFV`/`IMPF`/`PROSP`). These are *different* operators, not duplicates:
`Aspect`'s `PRFV` keeps intervals that *contain* the run-time (TSit ⊆ TT), whereas
`eventDenotation` keeps the run-time itself. The shared concept is homogeneity:
`eventDenotation_sub_stative` is the subinterval bound, the same property `Aspect`'s
imperfective denotations satisfy (`Studies/Giannakidou2002.lean` realises both sides
and now routes its perfective denotation through `eventDenotation`).
-/

namespace Tense.TemporalConnectives

variable {Time : Type*} [LinearOrder Time]

/-! ### The projection -/

/-- The event→interval projection: the set of run-time intervals of events satisfying
    `P`, i.e. the image of `P` under the temporal trace τ. Every event-level temporal
    connective theory projects down to the interval level through this map, where it can
    be compared with the Anscombe and Rett accounts. -/
def eventDenotation (P : Event Time → Prop) : SentDenotation Time :=
  Event.τ '' { e | P e }

/-- Membership in `eventDenotation`: an interval is a run-time of some `P`-event. -/
@[simp]
theorem mem_eventDenotation {P : Event Time → Prop} {i : NonemptyInterval Time} :
    i ∈ eventDenotation P ↔ ∃ e, P e ∧ e.τ = i := Iff.rfl

/-! ### Basic properties -/

/-- No events satisfy `P` ↔ the denotation is empty. -/
theorem eventDenotation_eq_empty {P : Event Time → Prop} :
    eventDenotation P = ∅ ↔ ∀ e, ¬ P e := by
  rw [eventDenotation, Set.image_eq_empty]
  exact Set.eq_empty_iff_forall_notMem

/-- The run-time of any `P`-event is in the denotation. -/
theorem mem_eventDenotation_of {P : Event Time → Prop} {e : Event Time} (he : P e) :
    e.τ ∈ eventDenotation P :=
  Set.mem_image_of_mem _ he

/-! ### Time trace factoring -/

/-- The time trace of an event denotation factors through τ: a time is in the trace iff
    some event satisfying `P` has a run-time containing it. This is the composition
    `timeTrace ∘ eventDenotation`, stating the full Level 3 → Level 1 projection directly. -/
theorem timeTrace_eventDenotation (P : Event Time → Prop) :
    timeTrace (eventDenotation P) = { t | ∃ e, P e ∧ t ∈ e.τ } := by
  ext t
  simp only [timeTrace, mem_eventDenotation, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, ⟨e, he, rfl⟩, hi⟩
    exact ⟨e, he, hi⟩
  · rintro ⟨e, he, hi⟩
    exact ⟨e.τ, ⟨e, he, rfl⟩, hi⟩

/-! ### Relationship to the canonical denotation patterns -/

/-- The image of a singleton event predicate (exactly one event, with run-time `i`) is
    the accomplishment denotation of `i`. This is `Set.image_singleton` for τ; it is a
    fact about a one-event predicate, not a characterisation of quantization in general. -/
theorem eventDenotation_singleton (e₀ : Event Time) :
    eventDenotation (fun e => e = e₀) = accomplishmentDenotation e₀.τ := by
  ext i
  simp only [mem_eventDenotation, accomplishmentDenotation, Set.mem_singleton_iff]
  constructor
  · rintro ⟨e, rfl, rfl⟩; rfl
  · intro h; exact ⟨e₀, rfl, h.symm⟩

/-- A predicate whose events all have run-time `≤ i` projects into a subset of the
    stative denotation of `i`.

    The inclusion is proper in general: `stativeDenotation i` contains every subinterval
    of `i`, including those that are the run-time of no event. -/
theorem eventDenotation_sub_stative (i : NonemptyInterval Time) (P : Event Time → Prop)
    (hP : ∀ e, P e → e.τ ≤ i) :
    eventDenotation P ⊆ stativeDenotation i := by
  rintro j ⟨e, he, rfl⟩
  exact hP e he

end Tense.TemporalConnectives
