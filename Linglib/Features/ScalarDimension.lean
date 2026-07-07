import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Order.Boundedness
import Linglib.Features.Aktionsart
import Linglib.Features.PropertyDomain
import Linglib.Features.Dimension

/-!
# Scalar dimensions

The axis a gradable predicate — an adjective, or a degree-achievement
verb's base adjective — measures along. One key with several views:
perceptual channel (`domain`, drives RSA noise), canonical scale shape
(`boundedness`), and the physical-quantity bridges (`physical?`,
`quotient?`).

Physical measurement dimensions (mass, volume-as-litres, …) are a
different fibration — an extensive ℚ-measure, not a gradable scale —
and live in `Features.Dimension`. The bridges are partial: evaluative
and psychological scales (`happiness`, `intelligence`) have no physical
dimension, which is why they reject ratio measure phrases ("six feet
tall" vs "*six feet happy"). `speed` is simplex here as a lexical scale
(*fast*) but a quotient physically ([bale-schwarz-2026]'s No Division
Hypothesis: the grammar does not compose the ratio).

The degree-theoretic apparatus over these dimensions (degree carriers,
telicity defaults, endpoint licensing) is in
`Semantics/Degree/Gradability/Dimension.lean`.
-/

namespace Features

open Core.Order (Boundedness)

/-- The scalar dimension a gradable predicate measures along — the union
    of the perceptual adjective dimensions and the scalar-change verb
    dimensions. -/
inductive ScalarDimension
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
def ScalarDimension.domain : ScalarDimension → PropertyDomain
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

/-- The dimension's canonical scale shape. Polarity/standard-type are not
    here — they live on the adjective entry (`min`/`max`-standard
    adjectives select a pole of a closed scale). Reducible so the degree
    fiber's `OrderTop`/`NoMaxOrder` instances synthesise through it. -/
abbrev ScalarDimension.boundedness : ScalarDimension → Boundedness
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

/-! ### Bridges to the physical quantity algebra -/

/-- The physical dimension a scalar dimension is measured in, when one
    exists: spatial scales are `distance`, `weight` is `mass`, `quantity`
    is `cardinality`. `none` for evaluative/psychological/state scales —
    the scales that reject ratio measure phrases. -/
def ScalarDimension.physical? : ScalarDimension → Option Dimension.Dimension
  | .height | .width | .length | .depth | .thickness => some .distance
  | .weight => some .mass
  | .age => some .time
  | .temperature => some .temperature
  | .quantity => some .cardinality
  | _ => none

/-- The quotient physical dimension, for lexical scales that are
    physically ratios: *fast* lexicalizes `speed = distance / time` as a
    primitive scale. -/
def ScalarDimension.quotient? : ScalarDimension → Option Dimension.QuotientDimension
  | .speed => some .speed
  | _ => none

/-- No scalar dimension is both simplex-physical and quotient-physical. -/
theorem ScalarDimension.physical_quotient_disjoint (d : ScalarDimension) :
    d.physical? = none ∨ d.quotient? = none := by
  cases d <;> simp [ScalarDimension.physical?, ScalarDimension.quotient?]

/-! ### Degree fiber and aspectual views ([kennedy-levin-2008])

Absorbed from the retired `Degree/Gradability/Dimension.lean`: the degree
carrier transports from `Boundedness.degreeShape`, and the Kennedy–Levin
telicity defaults are theorems about it. -/

open Core.Order (Boundedness LicensingPipeline)

/-- Each dimension's degree type — inherited from its boundedness, so the grounding
    transports rather than re-casing per dimension. -/
abbrev ScalarDimension.degree (d : ScalarDimension) : Type := d.boundedness.degreeShape
instance instLinearOrderDimensionDegree (d : ScalarDimension) : LinearOrder d.degree :=
  inferInstance

/-- The scale's order structure has a greatest element exactly when the dimension's
    canonical scale `HasMax` — grounded for all dimensions in one application. -/
theorem ScalarDimension.hasGreatest_degree_iff (d : ScalarDimension) :
    (∃ m : d.degree, IsTop m) ↔ d.boundedness.HasMax :=
  Boundedness.hasGreatest_degreeShape_iff d.boundedness

/-! ### Derived aspectual views (verb side) -/

/-- Default telicity of a degree achievement on this dimension: a scale with a
    greatest degree gives a telic reading ([kennedy-levin-2008]). -/
def ScalarDimension.defaultTelicity (d : ScalarDimension) : Telicity :=
  match d.boundedness with
  | .closed | .upperBounded => .telic
  | .open_ | .lowerBounded => .atelic

/-- Default Vendler class: degree achievements are dynamic and durative, so a
    closed scale gives an accomplishment, an open one an activity. -/
def ScalarDimension.defaultVendlerClass (d : ScalarDimension) : VendlerClass :=
  match d.boundedness with
  | .closed | .upperBounded => .accomplishment
  | .open_ | .lowerBounded => .activity

/-- **The Kennedy–Levin thesis as a theorem.** `defaultTelicity` is exactly the
    order-theoretic fact: a degree achievement is telic iff its scale's degree type
    has a greatest element — grounded in the scale's order structure, not stipulated. -/
theorem ScalarDimension.defaultTelicity_telic_iff_hasGreatest (d : ScalarDimension) :
    d.defaultTelicity = .telic ↔ ∃ m : d.degree, IsTop m := by
  rw [ScalarDimension.hasGreatest_degree_iff]; cases d <;> decide

/-! ### The endpoint: one more `LicensingPipeline` instance -/

instance : LicensingPipeline ScalarDimension where
  toBoundedness := ScalarDimension.boundedness

end Features
