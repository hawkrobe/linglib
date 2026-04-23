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
- Preconditions: states necessary for an event to be possible
- Consequences: states resulting from an event

These tests identify what's presupposed vs. what's asserted.

-/

import Linglib.Core.Semantics.Presupposition
import Linglib.Features.Acceptability
import Linglib.Paradigms.Measurement

namespace Phenomena.Presupposition.Diagnostics

open Features (Acceptability)
open Paradigms.Measurement

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
  judgment : Acceptability
  /-- What the judgment indicates -/
  interpretation : String
  deriving Repr


/--
The "allows for" test identifies preconditions (@cite{roberts-simons-2024} §2.1).

Frame: "ψ, which is part of what allows/allowed for φ"

If acceptable, ψ is an ontological precondition of the event in φ.
Preconditions are states that must hold for the event to be possible.

**Atelic caveat** (@cite{roberts-simons-2024} p. 711–712): For atelic target
verbs (e.g., *know*), the "allows for" frame can yield true readings for
concomitants due to a "definitional" sense of possibility. Fix: substitute
"come to V" to force a telic, inceptive interpretation. Example: use
"come to know" rather than "know" in the frame.
-/
def allowsForFrame : String := "_, which is part of what allowed for _"

/-- @cite{roberts-simons-2024} ex. 5a adapted to *stop*. -/
def allowsFor_stop_priorState : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "stop"
  , content := "prior state (was smoking)"
  , sentence := "John was smoking, which is part of what allowed for John to stop smoking"
  , judgment := .ok
  , interpretation := "Prior smoking is a precondition of stopping" }

/-- @cite{roberts-simons-2024} ex. 5a adapted to *start*. -/
def allowsFor_start_priorNonSmoker : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "start"
  , content := "prior state (wasn't smoking)"
  , sentence := "John had never smoked, which is part of what allowed for John to start smoking"
  , judgment := .ok
  , interpretation := "Prior non-smoking is a precondition of starting" }

/-- @cite{roberts-simons-2024} ex. 13a: selectional restriction passes. -/
def allowsFor_kick_hasFeet : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "kick"
  , content := "selectional restriction (has feet)"
  , sentence := "The robot has feet, which is part of what allowed for the robot to kick the tree"
  , judgment := .ok
  , interpretation := "Having feet is a precondition of kicking" }

/-- @cite{roberts-simons-2024} ex. 13b: concomitant fails. -/
def allowsFor_kick_touchedTree : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "kick"
  , content := "concomitant (touched the tree)"
  , sentence := "The robot touched the tree, which is part of what allowed for the robot to kick the tree"
  , judgment := .unacceptable
  , interpretation := "Touching is a concomitant (mereological part), not a precondition" }

/-- @cite{roberts-simons-2024} ex. 5b adapted: consequence fails "allows for". -/
def allowsFor_stop_consequence : DiagnosticResult :=
  { frame := allowsForFrame
  , trigger := "stop"
  , content := "result state (no longer smoking)"
  , sentence := "John no longer smokes, which is part of what allowed for John to stop smoking"
  , judgment := .unacceptable
  , interpretation := "Consequence doesn't 'allow for' — it temporally follows the event" }


/--
The counterfactual test confirms preconditions (@cite{roberts-simons-2024} §2.1).

Frame: "If not-ψ, it would not have been possible for [agent] to VP"

If acceptable, ψ is an ontological precondition: without it, the event
couldn't have occurred.
-/
def counterfactualFrame : String := "If not _, it would not have been possible for _ to _"

/-- "If the robot did not have feet, it would not have been possible
    for the robot to kick the tree." (T) -/
def counterfactual_kick_hasFeet : DiagnosticResult :=
  { frame := counterfactualFrame
  , trigger := "kick"
  , content := "selectional restriction (has feet)"
  , sentence := "If the robot did not have feet, it would not have been possible for the robot to kick the tree"
  , judgment := .ok
  , interpretation := "Having feet is a precondition of kicking (selectional restriction)" }

/-- "If John hadn't been ignorant of whether the jewels had been stolen,
    he couldn't have discovered that the jewels had been stolen." (T) -/
def counterfactual_discover_ignorance : DiagnosticResult :=
  { frame := counterfactualFrame
  , trigger := "discover"
  , content := "prior ignorance"
  , sentence := "If John hadn't been ignorant of whether the jewels had been stolen, he couldn't have discovered that the jewels had been stolen"
  , judgment := .ok
  , interpretation := "Prior ignorance is a precondition of discovering" }

/-- "If Yasmin had not been smoking, it would not have been possible
    for Yasmin to continue to smoke." (T) -/
def counterfactual_continue_priorActivity : DiagnosticResult :=
  { frame := counterfactualFrame
  , trigger := "continue"
  , content := "prior activity"
  , sentence := "If Yasmin had not been smoking, it would not have been possible for Yasmin to continue to smoke"
  , judgment := .ok
  , interpretation := "Prior activity is a precondition of continuing" }


/--
The "results in" test identifies consequences.

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
  , judgment := .ok
  , interpretation := "No longer smoking is a consequence (asserted content)" }

/-- "John started smoking results in him now being a smoker" -/
def resultsIn_start_nowSmoking : DiagnosticResult :=
  { frame := resultsInFrame
  , trigger := "start"
  , content := "result state (now smoking)"
  , sentence := "John started smoking results in him now being a smoker"
  , judgment := .ok
  , interpretation := "Now smoking is a consequence" }

/-- "John won the race results in him being the winner" -/
def resultsIn_win_winner : DiagnosticResult :=
  { frame := resultsInFrame
  , trigger := "win"
  , content := "winner status"
  , sentence := "John won the race results in him being the winner"
  , judgment := .ok
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
  , priorPassesAllowsFor := true   -- "was smoking, which allowed for stopping" ✓
  , priorFailsResultsIn := true    -- "stopping results in was smoker" ✗
  , resultPassesResultsIn := true  -- "stopping results in no longer smokes" ✓
  , resultFailsAllowsFor := true   -- "no longer smokes, which allowed for stopping" ✗
  }

/-- Pattern for "start" -/
def startPattern : PreconditionConsequencePattern :=
  { predicate := "start"
  , priorPassesAllowsFor := true   -- "never smoked, which allowed for starting" ✓
  , priorFailsResultsIn := true    -- "starting results in never smoked" ✗
  , resultPassesResultsIn := true  -- "starting results in now smokes" ✓
  , resultFailsAllowsFor := true   -- "now smokes, which allowed for starting" ✗
  }

/-- Pattern for "win" -/
def winPattern : PreconditionConsequencePattern :=
  { predicate := "win"
  , priorPassesAllowsFor := true   -- "was participant, which allowed for winning" ✓
  , priorFailsResultsIn := true    -- "winning results in participant" ✗
  , resultPassesResultsIn := true  -- "winning results in being winner" ✓
  , resultFailsAllowsFor := true   -- "being winner, which allowed for winning" ✗
  }

/--
The diagnostic pattern is uniform across predicates.

This suggests a systematic distinction between preconditions and consequences,
not an idiosyncratic property of individual lexical items.
-/
theorem patternIsUniform :
    stopPattern.priorPassesAllowsFor = startPattern.priorPassesAllowsFor ∧
    stopPattern.priorPassesAllowsFor = winPattern.priorPassesAllowsFor ∧
    stopPattern.resultPassesResultsIn = startPattern.resultPassesResultsIn ∧
    stopPattern.resultPassesResultsIn = winPattern.resultPassesResultsIn :=
  ⟨rfl, rfl, rfl, rfl⟩


/--
Content that passes "allows for" projects.

The precondition/consequence tests predict projection behavior:
- Preconditions (pass "allows for") → project through negation
- Consequences (pass "results in") → do not project through negation

Example:
- "John didn't stop smoking" still implies he was smoking (precondition projects)
- "John didn't stop smoking" does not imply he's not smoking (consequence doesn't project)
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
  , judgment := .ok
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
  , judgment := .ok
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
  , judgment := .ok
  , interpretation := "No global presupposition → filtered by antecedent" }


/--
The diagnostic tests and what they reveal.
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
  { name := "Counterfactual test"
  , testsFor := "Precondition status"
  , positiveIndicates := "Content is a precondition (event impossible without it)" },
  { name := "'Results in' test"
  , testsFor := "Consequence status"
  , positiveIndicates := "Content is a consequence (at-issue, doesn't project)" },
  { name := "Hey wait a minute!"
  , testsFor := "At-issueness"
  , positiveIndicates := "Content is not at-issue (backgrounded)" }
]

end Phenomena.Presupposition.Diagnostics
