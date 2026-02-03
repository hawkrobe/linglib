/-
# Presupposition Diagnostics

Empirical diagnostics for identifying and classifying projective content.

## Standard Diagnostics

1. **Family-of-Sentences** (Projection Test)
   - Negation: "It's not the case that P"
   - Question: "Is it the case that P?"
   - Modal: "It's possible that P"
   - Conditional: "If P, then Q"

   Content that survives these embeddings is projective.

2. **Hey Wait a Minute! Test** (At-Issueness)
   - At-issue content: challenged with "No, that's not true"
   - Not-at-issue content: challenged with "Hey wait a minute!"

3. **Belief Embedding Test** (OLE)
   - "x believes that S" — who is committed to the projective content?

## Precondition/Consequence Diagnostics

The "allows for" vs "results in" tests distinguish:
- **Preconditions**: States necessary for an event to be possible
- **Consequences**: States resulting from an event

These tests identify what's presupposed vs. what's asserted.

## References

- Karttunen (1973). Presuppositions of compound sentences.
- von Fintel (2004). Would you believe it? The king of France is back!
- Roberts & Simons (2024). Preconditions and projection.
- Tonhauser et al. (2013). Toward a taxonomy of projective content.
-/

import Linglib.Core.Presupposition

namespace Phenomena.Presupposition.Diagnostics

-- ============================================================================
-- PART 1: Judgment Types
-- ============================================================================

/--
Acceptability judgment for a diagnostic sentence.
-/
inductive Judgment where
  | acceptable      -- ✓ Natural, felicitous
  | marginal        -- ? Somewhat odd but interpretable
  | unacceptable    -- ✗ Infelicitous, odd
  deriving DecidableEq, Repr, BEq

/--
A diagnostic test result: sentence + judgment.
-/
structure DiagnosticResult where
  /-- The diagnostic frame used -/
  frame : String
  /-- The trigger being tested -/
  trigger : String
  /-- The content being probed -/
  content : String
  /-- Full sentence -/
  sentence : String
  /-- Native speaker judgment -/
  judgment : Judgment
  /-- What the judgment indicates -/
  interpretation : String
  deriving Repr

-- ============================================================================
-- PART 2: "Allows For" Diagnostic (Preconditions)
-- ============================================================================

/--
The "allows for" test identifies PRECONDITIONS.

Frame: "S allows for C"

If acceptable, C is a precondition of the event described by S.
Preconditions are states that must hold for the event to be possible,
but are not entailed to have caused the event.
-/
def allowsForFrame : String := "_ allows for _"

/-- "John stopped smoking allows for him to have been a heavy smoker" -/
def allowsFor_stop_priorHeavySmoker : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "stop"
  , content := "prior state (was smoking)"
  , sentence := "John stopped smoking allows for him to have been a heavy smoker"
  , judgment := .acceptable
  , interpretation := "Prior smoking is a precondition (can be elaborated)" }

/-- "John stopped smoking allows for him to have smoked for years" -/
def allowsFor_stop_priorDuration : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "stop"
  , content := "prior state duration"
  , sentence := "John stopped smoking allows for him to have smoked for 20 years"
  , judgment := .acceptable
  , interpretation := "Duration of prior state is compatible (precondition territory)" }

/-- "John started smoking allows for him to have never smoked before" -/
def allowsFor_start_priorNonSmoker : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "start"
  , content := "prior state (wasn't smoking)"
  , sentence := "John started smoking allows for him to have never smoked before"
  , judgment := .acceptable
  , interpretation := "Prior non-smoking is a precondition" }

/-- "John won the race allows for him to have been a participant" -/
def allowsFor_win_participant : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "win"
  , content := "participation"
  , sentence := "John won the race allows for him to have been a participant"
  , judgment := .acceptable
  , interpretation := "Being a participant is a precondition for winning" }

/-- "John stopped smoking allows for him to no longer smoke" — ODD -/
def allowsFor_stop_consequence : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "stop"
  , content := "result state (no longer smoking)"
  , sentence := "John stopped smoking allows for him to no longer smoke"
  , judgment := .unacceptable
  , interpretation := "Consequence doesn't 'allow for' — it's entailed" }

-- ============================================================================
-- PART 3: "Results In" Diagnostic (Consequences)
-- ============================================================================

/--
The "results in" test identifies CONSEQUENCES.

Frame: "S results in C"

If acceptable, C is a consequence of the event described by S.
Consequences are states that follow from the event occurring.
-/
def resultsInFrame : String := "_ results in _"

/-- "John stopped smoking results in him no longer smoking" -/
def resultsIn_stop_noLongerSmoking : DiagnosticResult :=
  { frame := resultsInFrame
  , trigger := "stop"
  , content := "result state (no longer smoking)"
  , sentence := "John stopped smoking results in him no longer smoking"
  , judgment := .acceptable
  , interpretation := "No longer smoking is a consequence (asserted content)" }

/-- "John started smoking results in him now being a smoker" -/
def resultsIn_start_nowSmoking : DiagnosticResult :=
  { frame := resultsInFrame
  , trigger := "start"
  , content := "result state (now smoking)"
  , sentence := "John started smoking results in him now being a smoker"
  , judgment := .acceptable
  , interpretation := "Now smoking is a consequence" }

/-- "John won the race results in him being the winner" -/
def resultsIn_win_winner : DiagnosticResult :=
  { frame := resultsInFrame
  , trigger := "win"
  , content := "winner status"
  , sentence := "John won the race results in him being the winner"
  , judgment := .acceptable
  , interpretation := "Being the winner is a consequence of winning" }

/-- "John stopped smoking results in him having been a smoker" — ODD -/
def resultsIn_stop_priorState : DiagnosticResult :=
  { frame := resultsInFrame
  , trigger := "stop"
  , content := "prior state (was smoking)"
  , sentence := "John stopped smoking results in him having been a smoker"
  , judgment := .unacceptable
  , interpretation := "Precondition doesn't 'result from' — it's presupposed" }

/-- "John started smoking results in him having never smoked" — ODD -/
def resultsIn_start_priorState : DiagnosticResult :=
  { frame := resultsInFrame
  , trigger := "start"
  , content := "prior state (never smoked)"
  , sentence := "John started smoking results in him having never smoked before"
  , judgment := .unacceptable
  , interpretation := "Precondition doesn't 'result from' — it's presupposed" }

-- ============================================================================
-- PART 4: Empirical Generalization
-- ============================================================================

/--
The precondition/consequence diagnostic pattern.

Empirical observation: For change-of-state predicates,
- Prior states pass "allows for" but fail "results in"
- Result states pass "results in" but fail "allows for"

This pattern holds across CoS verbs (stop, start, continue, finish, etc.)
-/
structure PreconditionConsequencePattern where
  /-- The predicate being tested -/
  predicate : String
  /-- Prior state passes "allows for" -/
  priorPassesAllowsFor : Bool
  /-- Prior state fails "results in" -/
  priorFailsResultsIn : Bool
  /-- Result state passes "results in" -/
  resultPassesResultsIn : Bool
  /-- Result state fails "allows for" -/
  resultFailsAllowsFor : Bool
  deriving Repr

/-- Pattern for "stop" -/
def stopPattern : PreconditionConsequencePattern :=
  { predicate := "stop"
  , priorPassesAllowsFor := true   -- "stop smoking allows for heavy smoker" ✓
  , priorFailsResultsIn := true    -- "stop smoking results in was smoker" ✗
  , resultPassesResultsIn := true  -- "stop smoking results in no longer smokes" ✓
  , resultFailsAllowsFor := true   -- "stop smoking allows for no longer smokes" ✗
  }

/-- Pattern for "start" -/
def startPattern : PreconditionConsequencePattern :=
  { predicate := "start"
  , priorPassesAllowsFor := true   -- "start smoking allows for never smoked" ✓
  , priorFailsResultsIn := true    -- "start smoking results in never smoked" ✗
  , resultPassesResultsIn := true  -- "start smoking results in now smokes" ✓
  , resultFailsAllowsFor := true   -- "start smoking allows for now smokes" ✗
  }

/-- Pattern for "win" -/
def winPattern : PreconditionConsequencePattern :=
  { predicate := "win"
  , priorPassesAllowsFor := true   -- "win race allows for participant" ✓
  , priorFailsResultsIn := true    -- "win race results in participant" ✗
  , resultPassesResultsIn := true  -- "win race results in winner" ✓
  , resultFailsAllowsFor := true   -- "win race allows for winner" ✗
  }

/--
The diagnostic pattern is uniform across predicates.

This suggests a systematic distinction between preconditions and consequences,
not an idiosyncratic property of individual lexical items.
-/
def patternIsUniform : Bool :=
  stopPattern.priorPassesAllowsFor == startPattern.priorPassesAllowsFor &&
  stopPattern.priorPassesAllowsFor == winPattern.priorPassesAllowsFor &&
  stopPattern.resultPassesResultsIn == startPattern.resultPassesResultsIn &&
  stopPattern.resultPassesResultsIn == winPattern.resultPassesResultsIn

-- ============================================================================
-- PART 5: Connection to Projection
-- ============================================================================

/--
Key empirical finding: Content that passes "allows for" projects.

The precondition/consequence tests predict projection behavior:
- Preconditions (pass "allows for") → project through negation
- Consequences (pass "results in") → do NOT project through negation

Example:
- "John didn't stop smoking" still implies he was smoking (precondition projects)
- "John didn't stop smoking" does NOT imply he's not smoking (consequence doesn't project)
-/
structure ProjectionPrediction where
  /-- Content type -/
  contentType : String
  /-- Passes "allows for" test -/
  passesAllowsFor : Bool
  /-- Projects through negation -/
  projectsThroughNegation : Bool
  /-- The two properties correlate -/
  correlation : Bool := passesAllowsFor == projectsThroughNegation
  deriving Repr

/-- Prior state of "stop": passes "allows for", projects -/
def priorStateProjection : ProjectionPrediction :=
  { contentType := "prior state (was smoking)"
  , passesAllowsFor := true
  , projectsThroughNegation := true }

/-- Result state of "stop": fails "allows for", doesn't project -/
def resultStateProjection : ProjectionPrediction :=
  { contentType := "result state (no longer smoking)"
  , passesAllowsFor := false
  , projectsThroughNegation := false }

-- ============================================================================
-- PART 6: Standard Presupposition Diagnostics
-- ============================================================================

/--
The negation test for presupposition.

Frame: "It's not the case that S"

If content C survives (is still implied), C is presupposed by S.
-/
def negationTestFrame : String := "It's not the case that _"

/-- "It's not the case that John stopped smoking" -/
def negationTest_stop : DiagnosticResult :=
  { frame := negationTestFrame
  , trigger := "stop"
  , content := "prior state (was smoking)"
  , sentence := "It's not the case that John stopped smoking"
  , judgment := .acceptable
  , interpretation := "Still implies John was smoking → prior state is presupposed" }

/--
The question test for presupposition.

Frame: "Is it the case that S?"

If content C survives (is still implied), C is presupposed by S.
-/
def questionTestFrame : String := "Is it the case that _?"

/-- "Did John stop smoking?" -/
def questionTest_stop : DiagnosticResult :=
  { frame := questionTestFrame
  , trigger := "stop"
  , content := "prior state (was smoking)"
  , sentence := "Did John stop smoking?"
  , judgment := .acceptable
  , interpretation := "Still implies John was smoking → prior state is presupposed" }

/--
The conditional test for presupposition filtering.

Frame: "If P, then S" where P entails the presupposition

If the presupposition is filtered (not globally projected), it shows
local satisfaction by the antecedent.
-/
def conditionalFilterFrame : String := "If _, then _"

/-- "If John was smoking, he stopped" -/
def conditionalTest_stop_filter : DiagnosticResult :=
  { frame := conditionalFilterFrame
  , trigger := "stop"
  , content := "prior state (was smoking)"
  , sentence := "If John was smoking, he stopped"
  , judgment := .acceptable
  , interpretation := "No global presupposition → filtered by antecedent" }

-- ============================================================================
-- PART 7: Summary of Diagnostic Tests
-- ============================================================================

/--
Summary: The key diagnostic tests and what they reveal.
-/
structure DiagnosticSummary where
  /-- Name of diagnostic -/
  name : String
  /-- What it tests for -/
  testsFor : String
  /-- Positive result indicates... -/
  positiveIndicates : String
  deriving Repr

def diagnosticTests : List DiagnosticSummary := [
  { name := "Negation test"
  , testsFor := "Projection"
  , positiveIndicates := "Content is presupposed (survives negation)" },
  { name := "Question test"
  , testsFor := "Projection"
  , positiveIndicates := "Content is presupposed (survives question)" },
  { name := "Conditional filter test"
  , testsFor := "Local satisfaction"
  , positiveIndicates := "Presupposition can be locally satisfied" },
  { name := "'Allows for' test"
  , testsFor := "Precondition status"
  , positiveIndicates := "Content is a precondition (projects)" },
  { name := "'Results in' test"
  , testsFor := "Consequence status"
  , positiveIndicates := "Content is a consequence (at-issue, doesn't project)" },
  { name := "Hey wait a minute!"
  , testsFor := "At-issueness"
  , positiveIndicates := "Content is not at-issue (backgrounded)" }
]

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Diagnostic Frames
- `allowsForFrame`: Tests for precondition status
- `resultsInFrame`: Tests for consequence status
- `negationTestFrame`: Tests for projection
- `questionTestFrame`: Tests for projection
- `conditionalFilterFrame`: Tests for local satisfaction

### Judgment Data
- `allowsFor_*`: Judgments for "allows for" frame
- `resultsIn_*`: Judgments for "results in" frame
- `negationTest_*`, `questionTest_*`: Standard projection tests

### Empirical Patterns
- `PreconditionConsequencePattern`: The diagnostic signature
- `stopPattern`, `startPattern`, `winPattern`: Specific predicates
- `patternIsUniform`: The pattern generalizes

### Key Finding
The "allows for" / "results in" tests reliably distinguish:
- **Preconditions**: Pass "allows for", fail "results in", PROJECT
- **Consequences**: Pass "results in", fail "allows for", DON'T PROJECT

This provides an empirical basis for the theoretical claim that
presuppositions are ontological preconditions.
-/

end Phenomena.Presupposition.Diagnostics
