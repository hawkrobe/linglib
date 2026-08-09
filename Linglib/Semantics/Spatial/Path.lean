import Linglib.Core.Order.Boundedness

/-!
# Spatial paths

Directed trajectories between locations: the spatial analog of temporal
intervals. [zwarts-2005]'s aspectual generalization — bounded directional PPs
(*to the store*) create telic VPs, unbounded ones (*towards the store*) atelic
VPs — enters through the `PathShape` classification and its bridge into scale
boundedness; the event-side telicity transfer lives in
`Semantics/Spatial/Trace.lean`.

## Main declarations

* `Path`: a directed trajectory with `source` and `goal` locations
  ([talmy-2000]'s path component of a motion event).
* `PathShape`: [zwarts-2005]'s boundedness classification of directional PPs
  (goal-, direction-, and origin-oriented), with `PathShape.toBoundedness`
  into `Core.Order.Boundedness`.
* `Path.adjacent`: endpoint-sharing spatial adjacency ([krifka-1998]), the
  spatial half of the movement relations in `Studies/Krifka1998.lean`.
-/

namespace Spatial

/-! ### Paths -/

/-- Spatial path: a directed trajectory between locations.
    [zwarts-2005]: paths are directed stretches of space with a
    source (starting point) and goal (endpoint).

    Parallels `NonemptyInterval` for the temporal domain. Unlike
    intervals, paths have no `valid : source ≤ goal` constraint
    because spatial locations lack a canonical linear ordering. -/
structure Path (Loc : Type*) where
  /-- Starting location of the path. -/
  source : Loc
  /-- Ending location of the path. -/
  goal : Loc

/-! ### Path shape -/

/-- Directional PP boundedness classification.
    [zwarts-2005]: the boundedness of a directional PP determines
    whether the VP it creates is telic or atelic.

    - `bounded`: goal-oriented ("to the store", "into the room")
    - `unbounded`: direction-oriented ("towards the store", "along the road")
    - `source`: origin-oriented ("from the store", "out of the room")

    This classifies the *set of paths* denoted by a PP, not individual
    paths, by closure under path concatenation: "towards X" denotes a
    cumulative set (concatenating two towards-X paths gives another),
    while "to X" strictly read denotes a set with no concatenable pairs
    at all. [zwarts-2005] shows bounded PPs are *not* quantized — a to-X
    path has proper to-X subpaths — so boundedness is non-cumulativity,
    not `Mereology.QUA`; see `Studies/Zwarts2005.lean`. -/
inductive PathShape where
  | bounded
  | unbounded
  | source
  deriving DecidableEq, Repr

/-- Path shape to scale boundedness: bounded/source paths correspond
    to closed scales, unbounded paths to open scales. -/
def PathShape.toBoundedness : PathShape → Core.Order.Boundedness
  | .bounded => .closed
  | .source => .closed
  | .unbounded => .open_

instance : Core.Order.LicensingPipeline PathShape where
  toBoundedness := PathShape.toBoundedness

/-! ### Adjacency -/

/-- Two paths are spatially adjacent (`∞_H` in [krifka-1998]'s notation)
    if they share an endpoint: one's goal is the other's source.
    Instantiates K98's abstract adjacency primitive for concrete paths;
    the spatial half of the movement relations in `Studies/Krifka1998.lean`. -/
def Path.adjacent {Loc : Type*} (p1 p2 : Path Loc) : Prop :=
  p1.goal = p2.source ∨ p2.goal = p1.source

/-- Path adjacency is symmetric. -/
theorem Path.adjacent_comm {Loc : Type*} {p1 p2 : Path Loc} :
    p1.adjacent p2 ↔ p2.adjacent p1 :=
  or_comm

/-- A path is adjacent to itself iff it is a single-point loop. -/
@[simp]
theorem Path.adjacent_self {Loc : Type*} {p : Path Loc} :
    p.adjacent p ↔ p.goal = p.source :=
  or_self_iff

end Spatial
