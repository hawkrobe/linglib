/-
# Empirical Data Types

Scale and task types for specifying empirical measures in phenomena data.
-/

import Linglib.Core.Word

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

-- ============================================================================
-- Processing Dimension Links
-- ============================================================================

/-- Processing dimensions that a task type is sensitive to.

Different experimental paradigms tap different processing dimensions.
This links `TaskType` to the dimensions in `ProcessingModel.ProcessingProfile`. -/
inductive ProcessingDimension where
  | locality        -- Distance-based effects (reading times, ERP latency)
  | boundaries      -- Clause boundary effects (CPS, wrap-up effects)
  | referentialLoad  -- Referential interference (similarity-based confusion)
  | ease            -- Retrieval facilitation (complexity benefits)
  deriving Repr, DecidableEq

/-- Which processing dimensions a task type is sensitive to.

Self-paced reading and eye-tracking are sensitive to locality and boundaries
(spillover regions, wrap-up effects). Acceptability ratings aggregate across
all dimensions. -/
def taskSensitiveDimensions : TaskType → List ProcessingDimension
  | .selfPacedReading => [.locality, .boundaries]
  | .eyeTracking      => [.locality, .boundaries, .referentialLoad]
  | .acceptabilityRating => [.locality, .boundaries, .referentialLoad, .ease]
  | .grammaticalityJudgment => [.locality, .boundaries, .referentialLoad, .ease]
  | _ => []  -- Other tasks not primarily about processing difficulty

/-- An empirical observation linked to processing dimensions.

Connects an observed behavioral measure to the processing profile dimensions
it reflects. -/
structure ProcessingObservation where
  /-- What was measured -/
  measure : MeasureSpec
  /-- Which processing dimensions this observation reflects -/
  dimensions : List ProcessingDimension
  /-- Description of the observed pattern -/
  description : String
  deriving Repr

end Phenomena
