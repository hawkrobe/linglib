/-!
# PropertyDomain — Perceptual/Cognitive Channels for Adjective Dimensions

[giles-etal-2026] [wolfe-horowitz-2017]

A taxonomy of perceptual and cognitive channels a gradable dimension belongs to.
`color`, `material`, and `orientation` are features known to guide visual search
([wolfe-horowitz-2017]); [giles-etal-2026] manipulates their perceptual
discriminability and finds colour resists reduction to discriminability alone.
These channels, together with `size`, are the dimensions parameterised by the
RSA reference-production studies; the remaining domains are inventoried for
typological completeness.

`PropertyDomain` is the codomain of `Features.ScalarDimension.domain`.
-/

namespace Features

/-- Broad perceptual/cognitive domain that a gradable dimension belongs to.
    `color`, `size`, `material`, and `orientation` are the perceptually
    parameterised domains in the reference-production studies; the rest are
    classified but not parameterised. -/
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
