/-!
# PropertyDomain — Perceptual/Cognitive Channels for Adjective Dimensions

[giles-etal-2026] [wolfe-horowitz-2017]

A taxonomy of perceptual and cognitive channels that classify the
dimension a gradable adjective measures along. `color`, `material`, and
`orientation` are features known to guide visual search
([wolfe-horowitz-2017]); [giles-etal-2026] manipulates their perceptual
discriminability and finds colour resists reduction to discriminability
alone. These channels, together with `size`, carry the noise parameters
used by the RSA reference model; the remaining domains are inventoried
for typological completeness.

`PerceptualDimension` names the individual dimensions (height, cost,
temperature, ...) and projects to a `PropertyDomain` via
`PerceptualDimension.domain`. The bridge to noise parameters
(`Features.PropertyDomain.noiseDiscrimination`) lives in
`Pragmatics/RSA/Channel.lean`.

## Main definitions

* `PropertyDomain` — the broad perceptual/cognitive channel.
* `PerceptualDimension` — a named scalar dimension, with a `domain` view.
-/

namespace Features

/-- Broad perceptual/cognitive domain that a gradable dimension belongs to.
    `color`, `size`, `material`, and `orientation` carry noise parameters
    in `RSA.Noise` (via `noiseDiscrimination`); the rest are classified but
    not parameterised. -/
inductive PropertyDomain where
  | color
  | size
  | material
  | orientation
  | sensory
  | evaluative
  | psychological
  | state
  deriving Repr, DecidableEq, Inhabited

/-- A named scalar dimension that a gradable adjective measures along.
    Used via leading-dot syntax in adjective entries
    (`{ ..., dimension := .height, ... }`); its perceptual channel is
    recovered with `PerceptualDimension.domain`. -/
inductive PerceptualDimension where
  -- Size
  | height | width | length | weight | thickness | depth | speed
  | strength | age | generalSize
  -- Sensory
  | temperature | brightness | volume
  -- Evaluative
  | happiness | cost | price | quality | value | danger | beauty
  | importance | safety
  -- Psychological
  | intelligence | expectation | possibility | confidence
  -- State
  | fullness | wetness | cleanliness | straightness | flatness | openness
  | freedom | tightness | alive | pregnancy | hardness | smoothness | purity
  | cracking | denting | scratching | shattering
  -- Perceptual (RSA noise connection)
  | color
  deriving Repr, DecidableEq, Inhabited

/-- The perceptual/cognitive channel a dimension belongs to. -/
def PerceptualDimension.domain : PerceptualDimension → PropertyDomain
  | .height | .width | .length | .weight | .thickness | .depth | .speed
  | .strength | .age | .generalSize => .size
  | .temperature | .brightness | .volume => .sensory
  | .happiness | .cost | .price | .quality | .value | .danger | .beauty
  | .importance | .safety => .evaluative
  | .intelligence | .expectation | .possibility | .confidence => .psychological
  | .fullness | .wetness | .cleanliness | .straightness | .flatness
  | .openness | .freedom | .tightness | .alive | .pregnancy | .hardness
  | .smoothness | .purity | .cracking | .denting | .scratching
  | .shattering => .state
  | .color => .color

end Features
