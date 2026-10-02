module

public import Linglib.Core.Order.Interval

/-!
# Events

Neo-Davidsonian event semantics ([davidson-1967], [parsons-1990]) quantifies over events, which
are individuals of their own sort: an event domain is a type `E`, verbs denote predicates on it,
and thematic roles relate its elements to their participants. The temporal trace `τ` sends each
event to its run time ([krifka-1998], [champollion-2017]). The trace need not be injective, since
two distinct events can go on at the same time.

## Main definitions

* `Event.TemporalTrace`: the temporal trace of an event domain.

## Implementation notes

* Parthood is an order on the event domain from `Semantics/Mereology.lean` (`PartialOrder`,
  `SemilatticeSup`, `Mereology.ClassicalMereology`). Laws relating it to the trace, such as the
  requirement of [krifka-1998] and [champollion-2017] that τ preserve sums, are hypotheses of the
  theorems that need them, and theories that never read a run time take no trace.
* τ is total, where [champollion-2017] lets trace functions be partial for events not located in
  time. The richness of [krifka-1998], that every time is the run time of some event, is
  `Function.Surjective τ`, a hypothesis where a theorem needs it.
* Run times are `NonemptyInterval T`, so the run time of a sum is the convex hull of the run times
  of its parts. In [krifka-1998] times form a part structure in which the sum of two separated
  times is not convex.
* [bach-1986] divides eventualities into states and non-states; here the division is a property
  of predicates (`Aspect.Dynamicity`, `Aspect.SortedProperty`), not a field of events.
* Intervals form an event domain with the identity trace, one event per run time, in which the
  studies build their satisfiability witnesses.

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
