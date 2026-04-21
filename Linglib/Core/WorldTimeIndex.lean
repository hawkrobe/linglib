import Mathlib.Tactic.TypeStar
import Linglib.Tactics.OntSort

/-!
# World–Time Indices

A `WorldTimeIndex` is a (world, time) pair used as a context of evaluation
for intensional, dynamic, modal, and tense semantics. This is the
Lewis/Kaplan-style "index of evaluation" with world and temporal
coordinates only — *not* the full Kratzer parthood-structured situation
(see `Core.IntensionalLogic.Situations`) and *not* the Pearl/Halpern
partial valuation (see `Core.Causal.Situation`).

The name `WorldTimeIndex` is preferred over `Situation` to disambiguate
from the two more substantive `Situation` types in those neighbouring
namespaces.
-/

namespace Core

/-- A world–time index: a (world, time) pair used as a context of
    evaluation in intensional, dynamic, modal, and tense semantics.

    This is the Lewis/Kaplan "index" — a coordinate tuple as point of
    evaluation, abstracting from the spatial/parthood structure of true
    Kratzer situations (see `Core.IntensionalLogic.Situations`). -/
@[ont_sort] structure WorldTimeIndex (W Time : Type*) where
  /-- The world coordinate -/
  world : W
  /-- The temporal coordinate -/
  time : Time
  deriving Repr

end Core
