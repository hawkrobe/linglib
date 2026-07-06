/-!
# PropertyDomain — Perceptual/Cognitive Channels for Adjective Dimensions

[giles-etal-2026] [wolfe-horowitz-2017]

A taxonomy of perceptual and cognitive channels a gradable dimension belongs to.
`color`, `material`, and `orientation` are features known to guide visual search
([wolfe-horowitz-2017]); [giles-etal-2026] manipulates their perceptual
discriminability and finds colour resists reduction to discriminability alone.
These channels, together with `size`, carry the noise parameters used by the RSA
reference model; the remaining domains are inventoried for typological
completeness.

`PropertyDomain` is the codomain of `Features.ScalarDimension.domain`; the
bridge to noise parameters (`Features.PropertyDomain.noiseDiscrimination`) lives in
`Pragmatics/RSA/Channel.lean`.
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

end Features
