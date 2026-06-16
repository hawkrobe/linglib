import Linglib.Core.Order.Boundedness

/-!
# Spatial Path Infrastructure
[gawron-2009] [talmy-2000] [zwarts-2005] [zwarts-winter-2000]

Framework-agnostic types for spatial paths and their boundedness
classification. Paths are the spatial analog of temporal intervals
(`NonemptyInterval`): directed stretches of space between locations.

The key linguistic insight: the boundedness of a directional
PP determines whether the VP it creates is telic or atelic. Bounded PPs
("to the store") yield telic VPs; unbounded PPs ("towards the store")
yield atelic VPs. This parallels the QUA/CUM mereological classification
from `Semantics/Mereology.lean`.

## Sections

1. Path Type
2. Path Shape (Boundedness Classification)
3. PathShape ↔ Scale Boundedness Bridge

-/

namespace Semantics.Spatial.Path

-- ════════════════════════════════════════════════════
-- § 1. Path Type
-- ════════════════════════════════════════════════════

set_option linter.dupNamespace false in
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

-- ════════════════════════════════════════════════════
-- § 2. Path Shape (Boundedness Classification)
-- ════════════════════════════════════════════════════

/-- Directional PP boundedness classification.
    [zwarts-2005]: the boundedness of a directional PP determines
    whether the VP it creates is telic or atelic.

    - `bounded`: goal-oriented ("to the store", "into the room")
    - `unbounded`: direction-oriented ("towards the store", "along the road")
    - `source`: origin-oriented ("from the store", "out of the room")

    This classifies the *set of paths* denoted by a PP, not individual
    paths. "To X" denotes {p | p.goal = X} — a QUA set (no proper
    subpath of a to-X path is also to-X). "Towards X" denotes a CUM
    set (concatenating two towards-X paths gives another). -/
inductive PathShape where
  | bounded
  | unbounded
  | source
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. PathShape ↔ Scale Boundedness Bridge
-- ════════════════════════════════════════════════════

/-- Path shape to scale boundedness: bounded/source paths correspond
    to closed scales, unbounded paths to open scales. Parallel to
    `quaBoundedness`/`cumBoundedness` in `Core/MereoDim.lean` §1. -/
def PathShape.toBoundedness : PathShape → Core.Order.Boundedness
  | .bounded => .closed
  | .source => .closed
  | .unbounded => .open_

/-- Bounded paths are licensed (closed scale → admits degree modification).
    [zwarts-2005]: "to the store" creates a telic VP because the path
    set is bounded, corresponding to a closed scale. -/
theorem bounded_path_licensed :
    PathShape.bounded.toBoundedness.IsLicensed := trivial

/-- Source paths are licensed (closed scale at the origin end). -/
theorem source_path_licensed :
    PathShape.source.toBoundedness.IsLicensed := trivial

/-- Unbounded paths are blocked (open scale → no inherent endpoint).
    [zwarts-2005]: "towards the store" creates an atelic VP because
    the path set is unbounded, corresponding to an open scale. -/
theorem unbounded_path_blocked :
    ¬ PathShape.unbounded.toBoundedness.IsLicensed := id

-- ════════════════════════════════════════════════════
-- § 4. Path Adjacency
-- ════════════════════════════════════════════════════

set_option linter.dupNamespace false in
/-- Two paths are spatially adjacent (`∞_H` in [krifka-1998]'s
    notation) if they share an endpoint: one's goal is the other's
    source. The general adjacency primitive ([krifka-1998] §2.3
    eq. 14) is axiomatized abstractly on a part structure; for the
    concrete `Path Loc` the share-an-endpoint definition is the
    intended instance. Used by K98 §4 movement-relation definitions
    (inlined in `Studies/Krifka1998.lean` Part II)
    to relate spatial adjacency on paths to temporal adjacency on events. -/
def Path.adjacent {Loc : Type*} (p1 p2 : Path Loc) : Prop :=
  p1.goal = p2.source ∨ p2.goal = p1.source

set_option linter.dupNamespace false in
/-- Path adjacency is symmetric. -/
theorem Path.adjacent_symm {Loc : Type*} (p1 p2 : Path Loc) :
    p1.adjacent p2 ↔ p2.adjacent p1 := by
  unfold Path.adjacent
  exact ⟨Or.symm, Or.symm⟩

set_option linter.dupNamespace false in
/-- A path is adjacent to itself when its source equals its goal
    (degenerate single-point path). Trivial corner case used in the
    K98 §4.5 SOURCE/GOAL definitions. -/
theorem Path.adjacent_trivial {Loc : Type*} (p : Path Loc)
    (h : p.source = p.goal) : p.adjacent p :=
  Or.inl h.symm

end Semantics.Spatial.Path
