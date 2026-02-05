/-
# Empirical Data Types

Scale and task types for specifying empirical measures in phenomena data.
-/

import Linglib.Core.Basic

namespace Phenomena

/-- Scale type for empirical measures. -/
inductive ScaleType where
  | binary
  | proportion
  | ordinal
  | continuous
  deriving Repr, DecidableEq

/-- Task type for data elicitation. -/
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

/-- Combined measure specification -/
structure MeasureSpec where
  scale : ScaleType
  task : TaskType
  /-- Unit or scale bounds (e.g., "percentage 0-100", "Likert 1-7", "ms") -/
  unit : String
  deriving Repr

end Phenomena
