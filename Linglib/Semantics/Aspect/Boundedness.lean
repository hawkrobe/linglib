import Linglib.Core.Order.Boundedness

/-!
# Aspectual boundedness

[smith-1997]

`SituationBoundedness` classifies a situation as bounded
(telic/perfective/closed) or unbounded (atelic/imperfective/open). It
cross-cuts Vendler classes and aspectual viewpoint, and is consumed by
event semantics, aspect theory, and temporal discourse interpretation.

The bridge to `Core.Order.MereoTag` (bounded ↔ quantized; unbounded ↔
cumulative) lets the licensing pipeline classify boundedness uniformly
with other scale-style properties.
-/

namespace Semantics.Aspect

/-- Aspectual boundedness of a situation.

    Whether a situation is conceptualized as having inherent boundaries:
    - **bounded**: telic / perfective / closed (achievements, accomplishments)
    - **unbounded**: atelic / imperfective / open (activities, states)

    Cross-cuts Vendler classes and aspectual viewpoint. Used by event
    semantics (telicity), aspect theory (perfective/imperfective), and
    temporal discourse interpretation (sequential vs. simultaneous default
    readings). -/
inductive SituationBoundedness where
  | bounded    -- telic / perfective / closed
  | unbounded  -- atelic / imperfective / open
  deriving DecidableEq, Repr

/-- SituationBoundedness → MereoTag: bounded = quantized, unbounded = cumulative.
    Bounded situations (telic/perfective) are mereologically quantized;
    unbounded situations (atelic/imperfective) are cumulative. -/
def SituationBoundedness.toMereoTag : SituationBoundedness → Core.Order.MereoTag
  | .bounded   => .qua
  | .unbounded => .cum

instance : Core.Order.LicensingPipeline SituationBoundedness where
  toBoundedness s := s.toMereoTag.toBoundedness

theorem bounded_licensed :
    Core.Order.LicensingPipeline.isLicensed SituationBoundedness.bounded = true := rfl

theorem unbounded_blocked :
    Core.Order.LicensingPipeline.isLicensed SituationBoundedness.unbounded = false := rfl

end Semantics.Aspect
