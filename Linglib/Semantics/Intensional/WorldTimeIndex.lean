import Linglib.Semantics.Dynamic.Possibility

/-!
# World–Time Indices

A `WorldTimeIndex` is a (world, time) pair used as a context of evaluation
for intensional, dynamic, modal, and tense semantics. This is the
Lewis/Kaplan-style "index of evaluation" with world and temporal
coordinates only — *not* the full Kratzer parthood-structured situation
(see `Intensional.Situations`) and *not* the Pearl/Halpern
partial valuation (see `Causation.Situation`).

The name `WorldTimeIndex` is preferred over `Situation` to disambiguate
from the two more substantive `Situation` types in those neighbouring
namespaces.
-/

namespace Intensional

/-- A world–time index: a (world, time) pair used as a context of
    evaluation in intensional, dynamic, modal, and tense semantics.

    This is the Lewis/Kaplan "index" — a coordinate tuple as point of
    evaluation, abstracting from the spatial/parthood structure of true
    Kratzer situations (see `Intensional.Situations`). -/
structure WorldTimeIndex (W Time : Type*) where
  /-- The world coordinate -/
  world : W
  /-- The temporal coordinate -/
  time : Time
  deriving Repr

/-- The point of index-dref dynamic semantics (`Tense/Dynamic.lean`,
`Mood/Dynamic.lean`): a `Possibility` whose world coordinate is the
current evaluation index and whose `ℕ`-registered drefs are also
world-time indices. Contexts are plain level-0 states
(`Set (WorldTimeIndex.Possibility W Time)`), so the update spine of
`Semantics/Dynamic/Update.lean` applies directly. -/
abbrev WorldTimeIndex.Possibility (W Time : Type*) :=
  DynamicSemantics.Possibility (WorldTimeIndex W Time) ℕ (WorldTimeIndex W Time)

end Intensional
