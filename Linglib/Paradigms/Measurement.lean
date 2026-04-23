/-!
# Paradigms.Measurement — Scale and Task Types for Empirical Measures

Cross-paradigm methodology types: scale of measurement, task type used
to elicit data, and a bundled `MeasureSpec`.

## Architectural note

`TaskType` enumerates experimental paradigms (self-paced reading, eye-
tracking, acceptability rating, …) — a domain that ought eventually to
be covered by anchored per-paradigm files (`Paradigms/SelfPacedReading.lean`,
`Paradigms/EyeTrackingReading.lean`, etc.) following the discipline laid
out in the `Paradigms/` README and `Paradigms/VisualWorld.lean` /
`Paradigms/AcceptabilityJudgment.lean`. Until those land, `TaskType` is
a low-discipline placeholder enum without per-paradigm-review anchoring.
Once a real `Paradigms/X.lean` file exists for one of the constructors,
that constructor should be removed from `TaskType` and call sites should
parameterise over the proper paradigm type instead.

`MeasureSpec` should similarly thin out as paradigm files specify their
own measurement contracts (e.g., `Paradigms/AcceptabilityJudgment.lean`'s
`DDResult` already replaces what a `MeasureSpec` would say about scale +
unit for AJ data).
-/

namespace Paradigms.Measurement

/-- Scale type for empirical measures. -/
inductive ScaleType where
  | binary
  | proportion
  | ordinal
  | continuous
  deriving Repr, DecidableEq

/-- Task type for data elicitation.

    Placeholder enum pending per-paradigm anchored files. -/
inductive TaskType where
  | grammaticalityJudgment
  | acceptabilityRating
  | truthValueJudgment
  | inferenceEndorsement
  | forcedChoice
  | production
  | selfPacedReading
  | eyeTracking
  | actOut
  deriving Repr, DecidableEq

/-- Combined measure specification: scale + task + unit string. -/
structure MeasureSpec where
  scale : ScaleType
  task : TaskType
  /-- Unit or scale bounds (e.g., "percentage 0-100", "Likert 1-7", "ms"). -/
  unit : String
  deriving Repr

end Paradigms.Measurement
