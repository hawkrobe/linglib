import Linglib.Semantics.Verb.Root.OutcomeCardinality
import Linglib.Semantics.Events.Basic
import Linglib.Semantics.ArgumentStructure.Thematic.Defs

/-!
# Root outcomes — event-relative machinery

The heavy, event-relative half of the outcome substrate: the boundary operators
`res`/`pre` and the outcome-bearing carrier `VerbOutcomes`. The light cardinality
invariant (`OutcomeCardinality`) lives in
`Semantics/Verb/Root/OutcomeCardinality.lean` so that `Root` can carry the
outcome axis without depending on `Event`/`EventRel`.

A verb root lexically encodes the **set of outcomes** its object can be in after
the action — the dimension [bhadra-2024] adds to root semantics, orthogonal to
the manner/result/cause kinds of [beavers-koontz-garboden-2020]'s
`Root.Kinds` (*bend* and *break* share a signature, differ in
outcomes).

## Main definitions

* `resState` / `preState` — an object's state at the right / left boundary of an
  event ([bhadra-2024], eqs. 64–65)
* `VerbOutcomes` — an outcome-bearing predicate: base predicate, outcome set,
  threshold set; `VerbOutcomes.cardinality` reads off its `OutcomeCardinality`

## References

* [bhadra-2024] (roots encode outcome sets)
-/

namespace ArgumentStructure

open Verb
open _root_.ArgumentStructure (EventRel)

/-! ### Event boundaries (eqs. 64–65)

`res` and `pre` read an object's lexically-relevant state (the paper's *state*
`k : t ↦ l(x)`, abstracted here as `State`) at the right and left boundaries of
an event's temporal trace `τ`. They are equivalence operators, not temporal
ones — they yield states, not times. -/

/-- A state function tracks an object's state at each time point. -/
abbrev StateFunction (Entity State Time : Type*) := Time → Entity → State

variable {Entity State Time : Type*} [LinearOrder Time]

/-- `res(e)(x)` (eq. 64): the object's state at the right boundary of `e`. -/
def resState (k : StateFunction Entity State Time) (e : Event Time) (x : Entity) : State :=
  k (Event.τ e).snd x

/-- `pre(e)(x)` (eq. 65): the object's state at the left boundary of `e`. -/
def preState (k : StateFunction Entity State Time) (e : Event Time) (x : Entity) : State :=
  k (Event.τ e).fst x

/-! ### The outcome-bearing verb root (the heavy witness)

An outcome-bearing predicate bundles the base predicate `P` (event-first, the
`⟨v,⟨e,t⟩⟩` meaning affixes modify) with the lexical outcome set `O` and the
contextual threshold set `T`. -/

/-- A verb root carrying an outcome set, the carrier result-state modifiers act
    on ([bhadra-2024], eqs. 56, 60). -/
structure VerbOutcomes (Entity State Time : Type*) [LinearOrder Time] where
  /-- The base predicate `P(e)(x)` (`⟨v,⟨e,t⟩⟩`). -/
  verb : EventRel Time Entity
  /-- The lexically-encoded outcome set `O` (states at the right boundary). -/
  outcomes : Set State
  /-- The contextual threshold set `T` (states at the left boundary). -/
  thresholds : Set State

/-- The cardinality tier of a root's outcome set. -/
noncomputable def VerbOutcomes.cardinality (vro : VerbOutcomes Entity State Time) :
    OutcomeCardinality :=
  OutcomeCardinality.ofSet vro.outcomes

end ArgumentStructure
