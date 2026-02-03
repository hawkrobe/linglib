/-
# Empirical Data Types and Linking Functions

Different empirical paradigms provide different kinds of evidence:
- Categorical judgments: "Is this grammatical?" (Yes/No)
- Graded acceptability: "How acceptable is this?" (1-7 scale)
- Processing measures: Reading times, eye-tracking, surprisal
- Choice data: Forced choice, production probabilities

A theory makes predictions by providing "linking functions"
that map theoretical constructs to predicted empirical measures.

## The Architecture

Theory → Linking Function → Predicted Data ↔ Observed Data

For example:
- CCG derivation depth → reading time prediction
- Feature unification cost → acceptability prediction
- Derivation probability → choice probability
- NeoGricean parameters → implicature rate prediction
-/

import Linglib.Core.Basic

namespace Phenomena

-- ============================================================================
-- Empirical Measure Types
-- ============================================================================

/-- Scale type: what kind of values are recorded -/
inductive ScaleType where
  | binary          -- yes/no, grammatical/ungrammatical
  | proportion      -- probability/percentage (0-1 or 0-100)
  | ordinal         -- ranked scale (e.g., 1-7 Likert)
  | continuous      -- continuous measure (reading time in ms, surprisal in bits)
  deriving Repr, DecidableEq

/-- Task type: how the measure was elicited -/
inductive TaskType where
  | grammaticalityJudgment    -- "Is this grammatical?"
  | acceptabilityRating       -- "Rate acceptability 1-7"
  | truthValueJudgment        -- "Is this true/false of the situation?"
  | inferenceEndorsement      -- "Does this imply X?"
  | forcedChoice              -- "Which object/referent?"
  | production                -- "What would you say?"
  | selfPacedReading          -- Reading time at each word
  | eyeTracking               -- Fixation times, regressions
  deriving Repr, DecidableEq

/-- Combined measure specification -/
structure MeasureSpec where
  scale : ScaleType
  task : TaskType
  /-- Unit or scale bounds (e.g., "percentage 0-100", "Likert 1-7", "ms") -/
  unit : String
  deriving Repr

/-- Legacy type alias for backwards compatibility -/
abbrev MeasureType := ScaleType

/-- A measured value with its type -/
inductive Measure where
  | binary : Bool → Measure                    -- categorical
  | ordinal : Nat → Nat → Measure              -- value, max_scale
  | realValued : Float → Measure               -- continuous
  | probability : Float → Measure              -- proportion [0,1]
  deriving Repr

-- ============================================================================
-- Data Points
-- ============================================================================

/-- A single empirical observation -/
structure DataPoint where
  /-- The linguistic stimulus -/
  stimulus : List Word
  /-- The condition/context -/
  condition : String
  /-- The measured value -/
  measure : Measure
  /-- Optional: participant/item info -/
  metadata : List (String × String) := []
  deriving Repr

/-- A dataset is a collection of data points -/
structure Dataset where
  name : String
  description : String
  measureType : MeasureType
  points : List DataPoint
  /-- Source citation -/
  source : String

-- ============================================================================
-- Graded Acceptability Data
-- ============================================================================

/-- Acceptability judgment with mean and standard error -/
structure AcceptabilityRating where
  stimulus : List Word
  condition : String
  mean : Float           -- mean rating
  se : Float             -- standard error
  n : Nat                -- number of participants
  scale : Nat := 7       -- scale maximum (typically 7)
  deriving Repr

/-- An acceptability judgment study -/
structure AcceptabilityStudy where
  name : String
  description : String
  source : String
  items : List AcceptabilityRating

-- ============================================================================
-- Processing Data (Reading Times, etc.)
-- ============================================================================

/-- A region in a self-paced reading or eye-tracking study -/
structure Region where
  words : List String
  position : Nat          -- region number in sentence
  deriving Repr

/-- Reading time data for a region -/
structure ReadingTime where
  stimulus : List Word
  region : Region
  condition : String
  meanRT : Float          -- mean reading time (ms)
  se : Float              -- standard error
  n : Nat
  deriving Repr

/-- Processing difficulty prediction -/
structure ProcessingPrediction where
  stimulus : List Word
  region : Region
  predictedDifficulty : Float
  deriving Repr

-- ============================================================================
-- Linking Functions (Theory → Data)
-- ============================================================================

/-- A linking function maps theoretical objects to predicted measures -/
class LinkingFunction (Theory : Type) (DataType : Type) where
  /-- Predict the empirical measure from the theory -/
  predict : Theory → DataType
  /-- Optional: specify what theoretical construct drives prediction -/
  mechanism : String := "unspecified"

/-- Categorical linking: derivability → grammaticality -/
class CategoricalLinking (G : Type) where
  /-- Does the grammar derive this string? -/
  derives : G → List Word → Bool
  /-- Prediction: derivable ↔ grammatical -/
  predictGrammatical : G → List Word → Bool := derives

/-- Graded linking: derivation complexity → acceptability -/
class GradedLinking (G : Type) where
  /-- Compute a complexity/cost measure for a derivation -/
  complexity : G → List Word → Option Float
  /-- Transform complexity to predicted acceptability -/
  -- Higher complexity → lower acceptability (negative correlation)
  predictAcceptability : G → List Word → Float

/-- Processing linking: incremental cost → reading time -/
class ProcessingLinking (G : Type) where
  /-- Compute incremental processing cost at each word -/
  incrementalCost : G → List Word → Nat → Float
  /-- Predict reading time from cost (linear linking assumption) -/
  predictRT (g : G) (ws : List Word) (pos : Nat) (baseline slope : Float) : Float :=
    baseline + slope * incrementalCost g ws pos

-- ============================================================================
-- Example: Derivation Depth as Complexity
-- ============================================================================

/-- Simple complexity measure: depth of derivation tree -/
def treeDepth : Nat → Float := λ n => n.toFloat

/-- Sprouse-style z-score acceptability -/
structure ZScoreRating where
  stimulus : List Word
  condition : String
  zScore : Float          -- standardized rating
  deriving Repr

-- ============================================================================
-- Connecting to Minimal Pairs
-- ============================================================================

/-- Extended minimal pair with graded judgments -/
structure GradedMinimalPair where
  /-- More acceptable variant -/
  better : List Word
  betterRating : Float
  /-- Less acceptable variant -/
  worse : List Word
  worseRating : Float
  /-- The clause type -/
  clauseType : ClauseType
  /-- Description of the contrast -/
  description : String
  deriving Repr

/-- Check if ratings match expected direction -/
def GradedMinimalPair.correctDirection (gmp : GradedMinimalPair) : Bool :=
  gmp.betterRating > gmp.worseRating

-- ============================================================================
-- Superadditivity (Sprouse Paradigm)
-- ============================================================================

/-
Sprouse et al.'s factorial design for island effects:
- Factor A: presence of island structure
- Factor B: presence of long-distance dependency

If the effect of A+B > effect of A + effect of B, we have superadditivity,
suggesting a grammatical constraint (not just processing difficulty).
-/

/-- A 2x2 factorial design for island effects -/
structure FactorialDesign where
  /-- Baseline: no island, no dependency -/
  baseline : AcceptabilityRating
  /-- Island only -/
  islandOnly : AcceptabilityRating
  /-- Dependency only -/
  depOnly : AcceptabilityRating
  /-- Both: island + dependency -/
  both : AcceptabilityRating
  deriving Repr

/-- Compute the interaction (superadditivity test) -/
def FactorialDesign.interaction (fd : FactorialDesign) : Float :=
  -- Difference-in-differences: is the combined effect larger than sum?
  let islandEffect := fd.baseline.mean - fd.islandOnly.mean
  let depEffect := fd.baseline.mean - fd.depOnly.mean
  let combinedEffect := fd.baseline.mean - fd.both.mean
  combinedEffect - (islandEffect + depEffect)

/-- Positive interaction suggests grammatical constraint -/
def FactorialDesign.isSuperadditive (fd : FactorialDesign) : Bool :=
  fd.interaction > 0

-- ============================================================================
-- Prediction Evaluation
-- ============================================================================

/-- Correlation between predictions and observations -/
structure PredictionEval where
  /-- Number of data points -/
  n : Nat
  /-- Correlation coefficient -/
  r : Float
  /-- Root mean squared error -/
  rmse : Float
  deriving Repr

/-- A theory captures graded data if predictions correlate with judgments -/
class CapturesGradedData (G : Type) [GradedLinking G] where
  grammar : G
  data : AcceptabilityStudy
  /-- Evidence that predictions match data -/
  eval : PredictionEval
  /-- Minimum acceptable correlation -/
  threshold : Float := 0.5
  /-- The correlation exceeds threshold -/
  meetsThreshold : eval.r > threshold := by decide

-- ============================================================================
-- Pragmatics Data Types
-- ============================================================================

/-
Pragmatic phenomena require data types that capture:
1. Speaker/listener choice distributions
2. Context-dependent interpretation
3. Implicature rates
4. Reference resolution accuracy
-/

/-- A context for pragmatic interpretation -/
structure PragContext where
  /-- Available referents in the discourse -/
  referents : List String
  /-- Prior beliefs/common ground -/
  commonGround : List String
  /-- The question under discussion (QUD) -/
  qud : Option String := none
  deriving Repr

/-- A speaker utterance choice -/
structure UtteranceChoice where
  /-- The utterance produced -/
  utterance : List Word
  /-- The intended meaning/referent -/
  intendedMeaning : String
  /-- The context -/
  context : PragContext
  deriving Repr

/-- Distribution over utterance choices -/
structure UtteranceDistribution where
  /-- Context -/
  context : PragContext
  /-- Intended meaning -/
  intendedMeaning : String
  /-- Utterances with their probabilities -/
  choices : List (List Word × Float)
  deriving Repr

/-- Listener interpretation data -/
structure InterpretationData where
  /-- The utterance heard -/
  utterance : List Word
  /-- The context -/
  context : PragContext
  /-- Interpretations with their probabilities -/
  interpretations : List (String × Float)
  deriving Repr

/-- Implicature derivation rate -/
structure ImplicatureRate where
  /-- The utterance -/
  utterance : List Word
  /-- The literal meaning -/
  literalMeaning : String
  /-- The strengthened/implicated meaning -/
  implicatedMeaning : String
  /-- Rate of implicature derivation (0-1) -/
  rate : Float
  /-- Number of participants -/
  n : Nat
  deriving Repr

/-- Reference resolution accuracy -/
structure ReferenceResolution where
  /-- The referring expression -/
  expression : List Word
  /-- Available referents -/
  referents : List String
  /-- Correct referent -/
  target : String
  /-- Accuracy (proportion choosing target) -/
  accuracy : Float
  /-- Response distribution -/
  distribution : List (String × Float)
  deriving Repr

-- ============================================================================
-- Production vs Comprehension Data
-- ============================================================================

/-- Production data: what speakers say -/
structure ProductionData where
  /-- The communicative goal/meaning -/
  goal : String
  /-- The context -/
  context : PragContext
  /-- Distribution of produced utterances -/
  productions : List (List Word × Float)
  /-- Number of participants -/
  n : Nat
  deriving Repr

/-- Comprehension data: how listeners interpret -/
structure ComprehensionData where
  /-- The heard utterance -/
  utterance : List Word
  /-- The context -/
  context : PragContext
  /-- Distribution of interpretations -/
  interpretations : List (String × Float)
  /-- Number of participants -/
  n : Nat
  deriving Repr

-- ============================================================================
-- Connecting Theory to Data
-- ============================================================================

/-
The full pipeline:
  Theory → Linking Function → Predicted Data ↔ Observed Data

1. Syntactic theory provides derivations
2. Semantic interpretation maps derivations to meanings
3. Pragmatic theory maps meanings + context to predictions
4. Linking functions connect predictions to behavioral data

This architecture allows:
- Testing syntactic theories against comprehension data
- Testing semantic theories against interpretation data
- Testing pragmatic theories against production/choice data
-/

end Phenomena
