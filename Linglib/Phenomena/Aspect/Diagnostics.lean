/-
# Aspectual Diagnostics

Empirical tests for determining aspectual class.

## Core Tests

| Test              | States | Activities | Achievements | Accomplishments |
|-------------------|--------|------------|--------------|-----------------|
| "for X"           | ✓      | ✓          | ✗            | ?               |
| "in X"            | ✗      | ✗          | ✓            | ✓               |
| Progressive       | ?      | ✓          | ?            | ✓               |
| "stop V-ing"      | ?      | ✓          | ?            | ✓               |
| Imperative        | ✗      | ✓          | ?            | ✓               |

## "For X" vs "In X" Tests

The classic tests from Vendler (1957) and Dowty (1979):

- "for an hour" — compatible with atelic predicates
  - "John ran for an hour" ✓ (activity)
  - "John knew French for ten years" ✓ (state)
  - *"John recognized Mary for an hour" ✗ (achievement)
  - ?"John built the house for a year" — coerced to activity

- "in an hour" — compatible with telic predicates
  - *"John ran in an hour" ✗ (activity, unless goal implied)
  - "John built the house in a year" ✓ (accomplishment)
  - "John recognized Mary in a second" ✓ (achievement)
  - *"John knew French in ten years" ✗ (state)

## Progressive Test

- Activities and accomplishments take the progressive naturally
- States typically resist the progressive (*"John is knowing French")
- Achievements take the progressive with special interpretations:
  - Slow-motion: "The bomb is exploding" (stretched out)
  - Preliminary stages: "John is dying" (process leading to death)

## References

- Vendler, Z. (1957). Verbs and times.
- Dowty, D. (1979). Word Meaning and Montague Grammar.
- Smith, C. (1991). The Parameter of Aspect.
- Rothstein, S. (2004). Structuring Events.
-/

import Linglib.Theories.Montague.Lexicon.Aspect

namespace Phenomena.Aspect.Diagnostics

open Montague.Lexicon.Aspect

-- ============================================================================
-- Diagnostic Results
-- ============================================================================

/--
Result of applying a diagnostic test.

- **Accept**: Test is felicitous (grammatical, acceptable)
- **Reject**: Test is infelicitous (ungrammatical, unacceptable)
- **Marginal**: Test is degraded but not completely out
- **Coerced**: Test is acceptable but requires meaning shift
-/
inductive DiagnosticResult where
  | accept    -- ✓ grammatical, acceptable
  | reject    -- ✗ ungrammatical, unacceptable
  | marginal  -- ? degraded, speaker variation
  | coerced   -- ~ acceptable with meaning shift
  deriving DecidableEq, Repr, BEq

/--
Convert Bool prediction to DiagnosticResult.
-/
def DiagnosticResult.fromBool : Bool → DiagnosticResult
  | true => .accept
  | false => .reject

-- ============================================================================
-- "For X" Adverbial Test
-- ============================================================================

/--
Prediction for "for X" adverbial compatibility.

"For X" measures the duration of an atelic (unbounded) eventuality:
- "ran for an hour" ✓
- "knew French for ten years" ✓
- *"arrived for an hour" ✗
- ?"built the house for a year" — coerces to repetitive

States and activities accept "for X" straightforwardly.
Achievements reject "for X" (no duration to measure).
Accomplishments can accept "for X" but with coercion to activity/repetition.
-/
def forXPrediction : VendlerClass → DiagnosticResult
  | .state => .accept
  | .activity => .accept
  | .achievement => .reject
  | .accomplishment => .coerced  -- "built houses for a year" = repeated building

/--
The "for X" test identifies atelic predicates.

States and activities pass; achievements fail; accomplishments require coercion.
-/
theorem forX_identifies_atelic (c : VendlerClass) :
    forXPrediction c = .accept ↔ c.telicity = .atelic := by
  cases c <;> simp [forXPrediction, VendlerClass.telicity]

-- ============================================================================
-- "In X" Adverbial Test
-- ============================================================================

/--
Prediction for "in X" adverbial compatibility.

"In X" measures time to reach a culmination point:
- *"ran in an hour" ✗ (no endpoint to reach)
- "arrived in an hour" ✓ (punctual, endpoint reached)
- "built the house in a year" ✓ (durative, endpoint reached)
- *"knew French in ten years" ✗ (no endpoint, state)

Only telic predicates have a culmination point to measure.
-/
def inXPrediction : VendlerClass → DiagnosticResult
  | .state => .reject
  | .activity => .reject
  | .achievement => .accept
  | .accomplishment => .accept

/--
The "in X" test identifies telic predicates.

Achievements and accomplishments pass; states and activities fail.
-/
theorem inX_identifies_telic (c : VendlerClass) :
    inXPrediction c = .accept ↔ c.telicity = .telic := by
  cases c <;> simp [inXPrediction, VendlerClass.telicity]

-- ============================================================================
-- Progressive Test
-- ============================================================================

/--
Prediction for progressive compatibility.

The progressive requires ongoing, dynamic eventualities:
- "John is running" ✓ (activity — paradigmatic)
- "John is building a house" ✓ (accomplishment — in progress)
- *"John is knowing French" ✗ (state — no stages)
- ?"John is arriving" — marginal (achievement, requires interpretation)

States generally reject the progressive (no stages, no development).
Achievements take the progressive marginally (slow-motion, preliminary).
-/
def progressivePrediction : VendlerClass → DiagnosticResult
  | .state => .reject
  | .activity => .accept
  | .achievement => .marginal  -- "The train is arriving" (preliminary stages)
  | .accomplishment => .accept

/--
The progressive test distinguishes dynamic and durative predicates.

Activities and accomplishments clearly accept; states reject;
achievements are marginal.
-/
theorem progressive_accepts_durative_dynamic (c : VendlerClass) :
    progressivePrediction c = .accept ↔
    (c.duration = .durative ∧ c.dynamicity = .dynamic) := by
  cases c <;> simp [progressivePrediction, VendlerClass.duration, VendlerClass.dynamicity]

-- ============================================================================
-- "Stop V-ing" Test
-- ============================================================================

/--
Prediction for "stop V-ing" compatibility.

"Stop V-ing" presupposes an ongoing activity that ceases:
- "John stopped running" ✓ (activity)
- "John stopped building the house" ✓ (accomplishment, activity in progress)
- ?"John stopped knowing French" — marginal (states don't "stop")
- ?"John stopped recognizing her" — requires iterative reading

This test identifies predicates with internal duration/stages.
-/
def stopVingPrediction : VendlerClass → DiagnosticResult
  | .state => .marginal  -- "stopped loving her" — requires inchoative reading
  | .activity => .accept
  | .achievement => .coerced  -- "stopped coughing" = stopped iterative coughing
  | .accomplishment => .accept

-- ============================================================================
-- Imperative Test
-- ============================================================================

/--
Prediction for imperative compatibility.

Imperatives require agentive control:
- "Run!" ✓ (activity)
- "Build a house!" ✓ (accomplishment)
- *"Know French!" ✗ (state, not controllable)
- ?"Recognize her!" — marginal (achievement, not directly controllable)
-/
def imperativePrediction : VendlerClass → DiagnosticResult
  | .state => .reject      -- States are not controllable
  | .activity => .accept
  | .achievement => .marginal  -- Some achievements are controllable
  | .accomplishment => .accept

-- ============================================================================
-- Full Diagnostic Battery
-- ============================================================================

/--
Result of running all diagnostic tests on a Vendler class.
-/
structure DiagnosticBattery where
  forX : DiagnosticResult
  inX : DiagnosticResult
  progressive : DiagnosticResult
  stopVing : DiagnosticResult
  imperative : DiagnosticResult
  deriving Repr, BEq

/--
Run all diagnostics for a Vendler class.
-/
def runDiagnostics (c : VendlerClass) : DiagnosticBattery :=
  { forX := forXPrediction c
  , inX := inXPrediction c
  , progressive := progressivePrediction c
  , stopVing := stopVingPrediction c
  , imperative := imperativePrediction c }

/--
Expected diagnostic battery for states.
-/
def stateDiagnostics : DiagnosticBattery :=
  { forX := .accept
  , inX := .reject
  , progressive := .reject
  , stopVing := .marginal
  , imperative := .reject }

/--
Expected diagnostic battery for activities.
-/
def activityDiagnostics : DiagnosticBattery :=
  { forX := .accept
  , inX := .reject
  , progressive := .accept
  , stopVing := .accept
  , imperative := .accept }

/--
Expected diagnostic battery for achievements.
-/
def achievementDiagnostics : DiagnosticBattery :=
  { forX := .reject
  , inX := .accept
  , progressive := .marginal
  , stopVing := .coerced
  , imperative := .marginal }

/--
Expected diagnostic battery for accomplishments.
-/
def accomplishmentDiagnostics : DiagnosticBattery :=
  { forX := .coerced
  , inX := .accept
  , progressive := .accept
  , stopVing := .accept
  , imperative := .accept }

/--
Running diagnostics on each class gives the expected battery.
-/
theorem diagnostics_correct (c : VendlerClass) :
    runDiagnostics c = match c with
      | .state => stateDiagnostics
      | .activity => activityDiagnostics
      | .achievement => achievementDiagnostics
      | .accomplishment => accomplishmentDiagnostics := by
  cases c <;> rfl

-- ============================================================================
-- Example Verb Data
-- ============================================================================

/--
Attested aspectual data for sample verbs.
-/
structure VerbAspectData where
  /-- Verb lemma -/
  lemma : String
  /-- Assigned Vendler class -/
  vendlerClass : VendlerClass
  /-- Example sentence for "for X" -/
  forXExample : String
  /-- Judgment for "for X" -/
  forXJudgment : DiagnosticResult
  deriving Repr

/-- "run" — activity -/
def runData : VerbAspectData :=
  { lemma := "run"
  , vendlerClass := .activity
  , forXExample := "John ran for an hour"
  , forXJudgment := .accept }

/-- "know" — state -/
def knowData : VerbAspectData :=
  { lemma := "know"
  , vendlerClass := .state
  , forXExample := "John knew French for ten years"
  , forXJudgment := .accept }

/-- "build" — accomplishment -/
def buildData : VerbAspectData :=
  { lemma := "build"
  , vendlerClass := .accomplishment
  , forXExample := "John built houses for ten years"
  , forXJudgment := .coerced }

/-- "arrive" — achievement -/
def arriveData : VerbAspectData :=
  { lemma := "arrive"
  , vendlerClass := .achievement
  , forXExample := "*John arrived for an hour"
  , forXJudgment := .reject }

/-- "recognize" — achievement -/
def recognizeData : VerbAspectData :=
  { lemma := "recognize"
  , vendlerClass := .achievement
  , forXExample := "*John recognized Mary for an hour"
  , forXJudgment := .reject }

/-- "love" — state -/
def loveData : VerbAspectData :=
  { lemma := "love"
  , vendlerClass := .state
  , forXExample := "John loved Mary for ten years"
  , forXJudgment := .accept }

/-- "write" — accomplishment (with bounded object) -/
def writeData : VerbAspectData :=
  { lemma := "write"
  , vendlerClass := .accomplishment
  , forXExample := "John wrote the book in two years"
  , forXJudgment := .coerced }

/-- All sample verb data -/
def allVerbData : List VerbAspectData :=
  [runData, knowData, buildData, arriveData, recognizeData, loveData, writeData]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Summary: Aspectual Diagnostics

### Core Tests
- `forXPrediction`: "for X" adverbial — identifies atelic predicates
- `inXPrediction`: "in X" adverbial — identifies telic predicates
- `progressivePrediction`: Progressive — requires durative + dynamic
- `stopVingPrediction`: "stop V-ing" — requires ongoing eventuality
- `imperativePrediction`: Imperative — requires agentivity

### Key Results
- `forX_identifies_atelic`: "for X" ↔ atelic
- `inX_identifies_telic`: "in X" ↔ telic
- `progressive_accepts_durative_dynamic`: Progressive ↔ durative ∧ dynamic
- `diagnostics_correct`: Full battery matches expected pattern

### Example Data
- `runData`, `knowData`, `buildData`, etc. — Sample verb annotations
- `allVerbData`: List of all sample data

### Usage
Import this module for empirical tests and example data.
Use `runDiagnostics` to get predictions for any Vendler class.
-/

end Phenomena.Aspect.Diagnostics
