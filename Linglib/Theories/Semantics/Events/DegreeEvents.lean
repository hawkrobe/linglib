import Linglib.Theories.Semantics.Events.Basic
import Linglib.Tactics.OntSort

/-!
# Degree Events (Zhao 2026, Ch. 4) @cite{zhao-2026}

Gradable predicates introduce events with degree traces τ_d parallel to
temporal traces τ_i. Comparison involves thematic roles [STD], [TAR], [DIFF]
that relate events to degree intervals.

This extends the neo-Davidsonian event ontology (`Ev`) with a degree
dimension, following Zhao's cross-domain parallel:

| Temporal domain           | Degree domain               |
|---------------------------|-----------------------------|
| τ_i : Event → Interval T | τ_d : Event → Interval D   |
| AGENT, THEME roles       | STD, TAR, DIFF roles        |
| States: ATOM-DIST_t      | Bare comp: ATOM-DIST_d      |

## References

- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation, Ch. 4.
-/

namespace Semantics.Events.DegreeEvents

open Core.Time
open Semantics.Events

/-- A degree event: an event with both temporal and degree traces.
    Extends the standard `Ev` (which has temporal trace τ_i = runtime)
    with a degree trace τ_d. -/
@[ont_sort] structure DegreeEv (Time Deg : Type*) [LE Time] [LE Deg] where
  /-- The underlying temporal event -/
  base : Ev Time
  /-- Degree trace: the interval on the degree scale spanned by this event -/
  degTrace : Interval Deg

/-- Temporal trace τ_i of a degree event (inherited from base). -/
@[simp]
def DegreeEv.τ_i {Time Deg : Type*} [LE Time] [LE Deg]
    (e : DegreeEv Time Deg) : Interval Time :=
  e.base.τ

/-- Degree trace τ_d of a degree event. -/
@[simp]
def DegreeEv.τ_d {Time Deg : Type*} [LE Time] [LE Deg]
    (e : DegreeEv Time Deg) : Interval Deg :=
  e.degTrace

/-- Comparison thematic roles (Zhao 2026, Ch. 4).
    In comparative constructions, events have participants playing
    degree-related roles analogous to standard thematic roles. -/
inductive ComparisonRole where
  | standard      -- [STD]: the standard of comparison ("than Mary")
  | target        -- [TAR]: the target of comparison ("John is taller")
  | differential  -- [DIFF]: the differential ("3 inches taller")
  deriving DecidableEq, Repr, BEq

/-- A predicate over degree events (not world-indexed). -/
abbrev DegEvPred (Time Deg : Type*) [LE Time] [LE Deg] :=
  DegreeEv Time Deg → Prop

/-- A world-indexed predicate over degree events. -/
abbrev DegEvPredW (W Time Deg : Type*) [LE Time] [LE Deg] :=
  W → DegreeEv Time Deg → Prop

/-- Existential closure for degree events. -/
def degExistsClosure {Time Deg : Type*} [LE Time] [LE Deg]
    (P : DegEvPred Time Deg) : Prop :=
  ∃ e : DegreeEv Time Deg, P e

end Semantics.Events.DegreeEvents
