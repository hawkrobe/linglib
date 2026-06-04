import Linglib.Core.Scales.Defs

/-!
# Scalar dimensions

A *dimension* is what a scalar (degree-achievement) verb's base adjective
measures — straightness, width, temperature, … . It is the categorical primitive
a fragment entry stores; the scale's **boundedness is not stored** but recovered
from the dimension as a derived view (`Dimension.boundedness`), grounded to the
order structure of the dimension's degree type in `Semantics/Aspect/ScalarTelicity.lean`.

This replaces storing `Boundedness` as a flag on each verb: distinct dimensions
that share a boundedness shape (e.g. `width` and `length`) stay distinct, and a
single physical quantity used on different scales is distinguished — *boil*
targets a bounded `boiling` scale, *cool*/*warm* an open `temperature` one.
-/

namespace ScalarTelicity

open Core.Scale (Boundedness)

/-- The scalar dimension a degree-achievement verb's base adjective measures. -/
inductive Dimension
  /-- Closed scales (a maximal degree exists → telic). -/
  | straightness | flatness | openness | cleanliness | curvature
  | cracking | denting | scratching | boiling
  /-- Open / unbounded-above scales (no maximal degree → atelic). -/
  | length | width | temperature | corrosion | quantity
  /-- No committed dimension (default). -/
  | unspecified
  deriving DecidableEq, Repr, BEq

/-- The boundedness shape of a dimension — a derived categorical view of whether
    its degree type has a greatest element. Grounded to the order mixin by
    `ScalarTelicity.hasGreatest_degree_iff_closed`. -/
def Dimension.boundedness : Dimension → Boundedness
  | .straightness | .flatness | .openness | .cleanliness | .curvature
  | .cracking | .denting | .scratching | .boiling => .closed
  | .length | .width | .temperature | .corrosion | .quantity
  | .unspecified => .open_

end ScalarTelicity
