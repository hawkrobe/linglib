import Linglib.Core.MeasurementScale

/-!
# Spatial Path Infrastructure

Framework-agnostic types for spatial paths and their boundedness
classification. Paths are the spatial analog of temporal intervals
(`Core.Time.Interval`): directed stretches of space between locations.

The key linguistic insight (Zwarts 2005): the boundedness of a directional
PP determines whether the VP it creates is telic or atelic. Bounded PPs
("to the store") yield telic VPs; unbounded PPs ("towards the store")
yield atelic VPs. This parallels the QUA/CUM mereological classification
from `Core/Mereology.lean`.

## Sections

1. Path Type
2. Path Shape (Boundedness Classification)
3. PathShape ↔ Scale Boundedness Bridge

## References

- Zwarts, J. & Winter, Y. (2000). Vector space semantics: a model-theoretic
  analysis of locative prepositions. *Journal of Logic, Language and
  Information* 9, 169–211.
- Zwarts, J. (2005). Prepositional aspect and the algebra of paths.
  *Linguistics and Philosophy* 28, 739–779.
- Gawron, J.M. (2009). Paths and scalar change.
- Talmy, L. (2000). *Toward a Cognitive Semantics*, Vol. II. MIT Press.
-/

namespace Core.Path

-- ════════════════════════════════════════════════════
-- § 1. Path Type
-- ════════════════════════════════════════════════════

set_option linter.dupNamespace false in
/-- Spatial path: a directed trajectory between locations.
    Zwarts (2005): paths are directed stretches of space with a
    source (starting point) and goal (endpoint).

    Parallels `Core.Time.Interval` for the temporal domain. Unlike
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
    Zwarts (2005): the boundedness of a directional PP determines
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
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. PathShape ↔ Scale Boundedness Bridge
-- ════════════════════════════════════════════════════

/-- Path shape to scale boundedness: bounded/source paths correspond
    to closed scales, unbounded paths to open scales. Parallel to
    `quaBoundedness`/`cumBoundedness` in `Core/MereoDim.lean` §1. -/
def PathShape.toBoundedness : PathShape → Core.Scale.Boundedness
  | .bounded => .closed
  | .source => .closed
  | .unbounded => .open_

/-- Bounded paths are licensed (closed scale → admits degree modification).
    Zwarts (2005): "to the store" creates a telic VP because the path
    set is bounded, corresponding to a closed scale. -/
theorem bounded_path_licensed :
    PathShape.bounded.toBoundedness.isLicensed = true := rfl

/-- Source paths are licensed (closed scale at the origin end). -/
theorem source_path_licensed :
    PathShape.source.toBoundedness.isLicensed = true := rfl

/-- Unbounded paths are blocked (open scale → no inherent endpoint).
    Zwarts (2005): "towards the store" creates an atelic VP because
    the path set is unbounded, corresponding to an open scale. -/
theorem unbounded_path_blocked :
    PathShape.unbounded.toBoundedness.isLicensed = false := rfl

end Core.Path
