module

public import Linglib.Core.Order.Interval

/-!
# Events

This file defines the temporal trace of an event domain. Neo-Davidsonian event semantics, after
Davidson and Parsons, quantifies over events as individuals of their own sort: an event domain is
a type `E`, verbs denote predicates on it, and thematic roles relate its events to their
participants. The temporal trace `τ` sends each event to its run time, as in Krifka and
Champollion, and need not be injective, since two distinct events can go on at the same time.

## Main definitions

* `Event.TemporalTrace`: the temporal trace of an event domain.

## Implementation notes

* Parthood is an order on the event domain from `Semantics/Mereology.lean`. Laws relating it to
  the trace, such as Krifka's and Champollion's requirement that τ preserve sums, are hypotheses
  of the theorems that need them, and theories that never read a run time take no trace.
* τ is total, where Champollion lets trace functions be partial. Krifka's richness, that every
  time is the run time of some event, is the hypothesis `Function.Surjective τ`.
* Run times are `NonemptyInterval T`, so the run time of a sum is the convex hull of the run times
  of its parts, where Krifka's times form a part structure with non-convex sums.
* Bach divides eventualities into states and non-states; here the division is a property of
  predicates (`Aspect.Dynamicity`, `Aspect.SortedProperty`), not a field of events.
* Intervals form an event domain with the identity trace, in which the studies build their
  satisfiability witnesses.

## References

* [davidson-1967]
* [parsons-1990]
* [bach-1986]
* [krifka-1998]
* [champollion-2017]
-/

@[expose] public section

namespace Event

/-- The temporal trace of an event domain `E`, which sends each event to its run time. -/
class TemporalTrace (E : Type*) (T : outParam Type*) [LE T] where
  /-- The run time of an event. -/
  τ : E → NonemptyInterval T

export TemporalTrace (τ)

/-- Each interval is an event whose run time is itself. -/
instance {T : Type*} [LE T] : TemporalTrace (NonemptyInterval T) T := ⟨id⟩

@[simp] theorem τ_nonemptyInterval {T : Type*} [LE T] (i : NonemptyInterval T) : τ i = i := rfl

end Event
