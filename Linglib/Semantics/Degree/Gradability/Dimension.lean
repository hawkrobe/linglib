import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Order.Boundedness
import Linglib.Features.Aktionsart
import Linglib.Features.PropertyDomain
import Linglib.Semantics.Degree.Bounds

/-!
# Scalar dimensions

The axis a gradable predicate — an adjective, or a degree-achievement verb's base
adjective — measures along. This is the single carrier the former
`Features.PerceptualDimension` (perceptual channel) and `ScalarTelicity.Dimension`
(scale structure) were both approximating; they are unified here so that RSA noise,
adjective comparison-class dependence, and verb telicity are all *views of one key*.

Physical measurement dimensions (mass, volume-as-litres, …) are a different
fibration — an extensive ℚ-measure, not a gradable scale — and stay in
`Features.Dimension`.

## Views

* `Dimension.domain` — the perceptual/cognitive channel (drives RSA noise via
  `Features.PropertyDomain.noiseDiscrimination`).
* `Dimension.boundedness` — the canonical scale shape, the derived source of both
  adjective standard-type and verb telicity.
* `Dimension.degree` — a computable order-proxy for the scale, grounded to
  `boundedness` by `hasGreatest_degree_iff`; only the `OrderTop`/`NoMaxOrder` mixin
  is meaningful, not the carrier ([kennedy-levin-2008]).

`Dimension` is one more `Core.Order.LicensingPipeline` instance, so it shares the
endpoint-licensing pipeline with `Boundedness`, `MereoTag`, and `EpistemicTag`.
-/

open Core.Order (Boundedness ScalePolarity LicensingPipeline)
open Degree (HasGreatest hasGreatest_of_orderTop not_hasGreatest_of_noMaxOrder)
open Features (Telicity VendlerClass)

namespace Semantics.Gradability

/-- The scalar dimension a gradable predicate measures along — the union of the
    perceptual adjective dimensions and the scalar-change verb dimensions. -/
inductive Dimension
  -- Size
  | height | width | length | weight | thickness | depth | speed | strength
  | age | generalSize
  -- Sensory
  | temperature | brightness | volume
  -- Evaluative
  | happiness | cost | price | quality | value | danger | beauty | importance | safety
  -- Psychological
  | intelligence | expectation | possibility | confidence
  -- State (adjective + deadjectival-verb change dimensions)
  | fullness | wetness | cleanliness | straightness | flatness | openness
  | freedom | tightness | alive | pregnancy | hardness | smoothness | purity
  | cracking | denting | scratching | shattering
  -- Perceptual colour + verb-only scalar-change dimensions
  | color | curvature | boiling | corrosion | quantity | unspecified
  deriving DecidableEq, Repr, Fintype, Inhabited, BEq

/-- The perceptual/cognitive channel — drives RSA noise. -/
def Dimension.domain : Dimension → Features.PropertyDomain
  | .height | .width | .length | .weight | .thickness | .depth | .speed
  | .strength | .age | .generalSize | .quantity => .size
  | .temperature | .brightness | .volume => .sensory
  | .happiness | .cost | .price | .quality | .value | .danger | .beauty
  | .importance | .safety => .evaluative
  | .intelligence | .expectation | .possibility | .confidence => .psychological
  | .fullness | .wetness | .cleanliness | .straightness | .flatness | .openness
  | .freedom | .tightness | .alive | .pregnancy | .hardness | .smoothness | .purity
  | .cracking | .denting | .scratching | .shattering
  | .curvature | .boiling | .corrosion | .unspecified => .state
  | .color => .color

/-- The dimension's canonical scale shape. Polarity/standard-type are not here —
    they live on the adjective entry (`min`/`max`-standard adjectives select a pole
    of a closed scale). Reducible so the `degree` fiber's `OrderTop`/`NoMaxOrder`
    instances synthesise through it. -/
abbrev Dimension.boundedness : Dimension → Boundedness
  | .straightness | .flatness | .openness | .cleanliness | .curvature
  | .cracking | .denting | .scratching | .boiling
  | .alive | .freedom | .fullness | .purity | .shattering | .smoothness
  | .tightness | .wetness | .pregnancy => .closed
  | .height | .width | .length | .weight | .thickness | .depth | .speed
  | .strength | .age | .generalSize | .temperature | .brightness | .volume
  | .happiness | .cost | .price | .quality | .value | .danger | .beauty
  | .importance | .safety | .intelligence | .expectation | .possibility
  | .confidence | .hardness | .color | .corrosion | .quantity
  | .unspecified => .open_

/-! ### Degree fiber, grounded through `Boundedness` (proved once, not per dimension) -/

/-- Degree carrier per boundedness shape: a greatest element exists exactly when the
    scale `HasMax`. A computable order-proxy — only the `OrderTop`/`NoMaxOrder` mixin
    matters, not the carrier. -/
abbrev _root_.Core.Order.Boundedness.degreeShape : Boundedness → Type
  | .open_ | .lowerBounded => ℕ
  | .upperBounded | .closed => WithTop ℕ

instance (b : Boundedness) : LinearOrder b.degreeShape := by cases b <;> exact inferInstance

/-- **Grounding, proved once at the 4-case level.** -/
theorem _root_.Core.Order.Boundedness.hasGreatest_degreeShape_iff (b : Boundedness) :
    HasGreatest b.degreeShape ↔ b.HasMax := by
  cases b
  · exact iff_of_false not_hasGreatest_of_noMaxOrder (by decide)
  · exact iff_of_false not_hasGreatest_of_noMaxOrder (by decide)
  · exact iff_of_true hasGreatest_of_orderTop (by decide)
  · exact iff_of_true hasGreatest_of_orderTop (by decide)

/-- Each dimension's degree type — inherited from its boundedness, so the grounding
    transports rather than re-casing per dimension. -/
abbrev Dimension.degree (d : Dimension) : Type := d.boundedness.degreeShape
instance (d : Dimension) : LinearOrder d.degree := inferInstance

/-- The scale's order structure has a greatest element exactly when the dimension's
    canonical scale `HasMax` — grounded for all dimensions in one application. -/
theorem Dimension.hasGreatest_degree_iff (d : Dimension) :
    HasGreatest d.degree ↔ d.boundedness.HasMax :=
  Boundedness.hasGreatest_degreeShape_iff d.boundedness

/-! ### Derived aspectual views (verb side) -/

/-- Default telicity of a degree achievement on this dimension: a scale with a
    greatest degree gives a telic reading ([kennedy-levin-2008]). -/
def Dimension.defaultTelicity (d : Dimension) : Telicity :=
  match d.boundedness with
  | .closed | .upperBounded => .telic
  | .open_ | .lowerBounded => .atelic

/-- Default Vendler class: degree achievements are dynamic and durative, so a
    closed scale gives an accomplishment, an open one an activity. -/
def Dimension.defaultVendlerClass (d : Dimension) : VendlerClass :=
  match d.boundedness with
  | .closed | .upperBounded => .accomplishment
  | .open_ | .lowerBounded => .activity

/-- **The Kennedy–Levin thesis as a theorem.** `defaultTelicity` is exactly the
    order-theoretic fact: a degree achievement is telic iff its scale's degree type
    has a greatest element — grounded in the scale's order structure, not stipulated. -/
theorem Dimension.defaultTelicity_telic_iff_hasGreatest (d : Dimension) :
    d.defaultTelicity = .telic ↔ HasGreatest d.degree := by
  rw [Dimension.hasGreatest_degree_iff]; cases d <;> decide

/-! ### The endpoint: one more `LicensingPipeline` instance -/

instance : LicensingPipeline Dimension where
  toBoundedness := Dimension.boundedness

end Semantics.Gradability
