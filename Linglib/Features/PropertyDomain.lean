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
* `PropertyDomain.requiresComparisonClass` — coarse relative/absolute tag.
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

/-- Whether adjectives in this domain are typically **relative** gradable
    adjectives, whose standard is fixed against a contextual comparison
    class ([kennedy-2007], [kennedy-mcnally-2005]). Size, evaluative,
    psychological, and sensory domains are relative; color, material,
    orientation, and state are absolute — the standard sits at a scale
    endpoint, or the adjective is non-gradable.

    This is a coarse domain-keyed heuristic. The principled classification
    runs off scale structure, not perceptual domain:
    `Semantics.Degree.PositiveStandard.RequiresComparisonClass` derives the
    same distinction from an adjective's `Boundedness`, and the two can
    diverge (mildly-positive adjectives such as *decent* receive a
    functional standard the domain heuristic misses). The heuristic also
    collapses the maximum-standard, minimum-standard, and non-gradable
    distinctions ([rotstein-winter-2004]) into a single `False`. -/
def PropertyDomain.requiresComparisonClass : PropertyDomain → Prop
  | .size          => True   -- tall, short, big, wide, ...
  | .evaluative    => True   -- expensive, good, ...
  | .psychological => True   -- smart, ...
  | .sensory       => True   -- hot, cold, ...
  | .color         => False  -- yellow, red, ...
  | .material      => False  -- wooden, metal, ...
  | .orientation   => False  -- vertical, horizontal, ...
  | .state         => False  -- full, wet, dead, ...

instance : DecidablePred PropertyDomain.requiresComparisonClass
  | .size          => inferInstanceAs (Decidable True)
  | .evaluative    => inferInstanceAs (Decidable True)
  | .psychological => inferInstanceAs (Decidable True)
  | .sensory       => inferInstanceAs (Decidable True)
  | .color         => inferInstanceAs (Decidable False)
  | .material      => inferInstanceAs (Decidable False)
  | .orientation   => inferInstanceAs (Decidable False)
  | .state         => inferInstanceAs (Decidable False)

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
