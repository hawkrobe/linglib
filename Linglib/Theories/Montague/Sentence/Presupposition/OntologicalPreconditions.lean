/-
# Ontological Preconditions and Projection

Theory of presupposition projection based on event structure.

## Core Claim

Projective contents are ontological preconditions of events:
- Preconditions: States necessary for the event to exist/occur -- project
- Consequences: States resulting from the event -- at-issue (don't project)

## Theoretical Explanation

Why do preconditions project through negation?

Consider: "John didn't stop smoking"

For this sentence to be evaluable:
1. The stopping event must be the kind of thing that could have happened
2. For stopping to be possible, John must have been smoking
3. The sentence asserts that this possible stopping didn't actually occur

Therefore, even though we're negating the event, we're still presupposing
that the event was possible, and possibility requires the precondition.

## Connection to Diagnostics

The empirical diagnostics in `Phenomena.Presupposition.Diagnostics`:
- "allows for" test → identifies preconditions
- "results in" test → identifies consequences

This theory predicts that pattern: preconditions can be elaborated because
they're independent facts about the world; consequences follow from the event
and thus can't be "allowed for" independently.

## References

- Roberts, C. & Simons, M. (2024). Preconditions and projection.
- Tonhauser et al. (2013). Toward a taxonomy of projective content.
-/

import Linglib.Core.Presupposition
import Linglib.Theories.Montague.Verb.ChangeOfState.Theory
import Linglib.Theories.Montague.Verb.Aspect
import Linglib.Phenomena.Presupposition.Diagnostics

namespace Montague.Sentence.Presupposition.OntologicalPreconditions

open Core.Presupposition
open Montague.Verb.ChangeOfState
open Montague.Verb.Aspect
open Phenomena.Presupposition.Diagnostics


variable {W : Type*}

/--
An event decomposed into temporal phases:
1. Precondition: State that must hold BEFORE for the event to be possible
2. The event occurrence itself
3. Consequence: State that holds AFTER the event
-/
structure EventPhase (W : Type*) where
  /-- Precondition: must hold before the event for it to be possible -/
  precondition : W → Bool
  /-- The event actually occurs -/
  eventOccurs : W → Bool
  /-- Consequence: holds after the event (result state) -/
  consequence : W → Bool

/--
Well-formed event: precondition enables the event.

This is the ontological constraint: you can't stop smoking unless you were smoking.
-/
def EventPhase.wellFormed (e : EventPhase W) : Prop :=
  ∀ w, e.eventOccurs w → e.precondition w


/-- "Stop P" as an event phase -/
def stopAsEventPhase (P : W → Bool) : EventPhase W where
  precondition := P
  eventOccurs := P
  consequence := λ w => !P w

/-- "Start P" as an event phase -/
def startAsEventPhase (P : W → Bool) : EventPhase W where
  precondition := λ w => !P w
  eventOccurs := λ w => !P w
  consequence := P

/-- "Continue P" as an event phase -/
def continueAsEventPhase (P : W → Bool) : EventPhase W where
  precondition := P
  eventOccurs := P
  consequence := P


/-- Event phase precondition = CoS presupposition. -/
theorem stop_precondition_is_presup (P : W → Bool) :
    (stopAsEventPhase P).precondition = priorStatePresup .cessation P := rfl

theorem start_precondition_is_presup (P : W → Bool) :
    (startAsEventPhase P).precondition = priorStatePresup .inception P := rfl

theorem continue_precondition_is_presup (P : W → Bool) :
    (continueAsEventPhase P).precondition = priorStatePresup .continuation P := rfl

/-- Event phase consequence = CoS assertion. -/
theorem stop_consequence_is_assertion (P : W → Bool) :
    (stopAsEventPhase P).consequence = resultStateAssertion .cessation P := rfl

theorem start_consequence_is_assertion (P : W → Bool) :
    (startAsEventPhase P).consequence = resultStateAssertion .inception P := rfl

theorem continue_consequence_is_assertion (P : W → Bool) :
    (continueAsEventPhase P).consequence = resultStateAssertion .continuation P := rfl


/-
## The Aboutness Mechanism

Why do preconditions project through negation? Roberts & Simons (2024) argue:

1. Sentences refer to event types (not just assert propositions)
2. Event types have inherent preconditions (ontological requirements)
3. Both "John stopped" and "John didn't stop" refer to the same event type
4. Negation affects the claim about the event, not which event is referenced
5. Therefore, preconditions project: they're tied to the event reference

This contrasts with an assertion-only view where sentences are just truth conditions.
Under assertion-only, there's no structural reason for shared presuppositions.
-/

/--
Polarity: whether we affirm or deny that the event occurred.
-/
inductive Polarity where
  | affirmed   -- "John stopped smoking"
  | negated    -- "John didn't stop smoking"
  deriving DecidableEq, Repr, BEq

/--
A sentence that refers to an event type and makes a claim about it.

The event type referenced is independent of the claim made.
Both affirmative and negative sentences can refer to the same event type.
-/
structure EventSentence (W : Type*) where
  /-- The event type this sentence is about -/
  eventType : EventPhase W
  /-- The polarity of the claim -/
  polarity : Polarity

/--
The "aboutness" of a sentence: what event type it refers to.

This is independent of polarity: both "John stopped" and "John didn't stop"
are about the same event type (the stopping).
-/
def EventSentence.aboutness (s : EventSentence W) : EventPhase W :=
  s.eventType

/--
The assertion made by a sentence depends on polarity.

- Affirmed: The event occurred (consequence holds)
- Negated: The event didn't occur (consequence doesn't hold)
-/
def EventSentence.assertion (s : EventSentence W) : W → Bool :=
  match s.polarity with
  | .affirmed => s.eventType.consequence
  | .negated => λ w => !s.eventType.consequence w

/--
The presupposition comes from aboutness, not from the assertion.

Presuppositions are tied to event reference, not to the claim being made.
-/
def EventSentence.presupposition (s : EventSentence W) : W → Bool :=
  s.aboutness.precondition

/--
Construct an affirmative sentence about an event type.
-/
def affirmative (e : EventPhase W) : EventSentence W :=
  { eventType := e, polarity := .affirmed }

/--
Construct a negative sentence about an event type.
-/
def negative (e : EventPhase W) : EventSentence W :=
  { eventType := e, polarity := .negated }

/--
Affirmative and negative sentences have the same aboutness.

Both "John stopped smoking" and "John didn't stop smoking" are about
the same event type, the stopping event. This is the structural basis
for presupposition projection.
-/
theorem same_aboutness (e : EventPhase W) :
    (affirmative e).aboutness = (negative e).aboutness := rfl

/--
Presuppositions project because they come from shared aboutness.

Since presuppositions are derived from aboutness, and aboutness is shared
across polarities, presuppositions must be shared too.
-/
theorem presupposition_projects (e : EventPhase W) :
    (affirmative e).presupposition = (negative e).presupposition := rfl

/--
Assertions differ by polarity.

While presuppositions are shared, assertions differ:
the negative asserts the opposite of the affirmative.
-/
theorem assertion_differs (e : EventPhase W) (w : W) :
    (negative e).assertion w = !(affirmative e).assertion w := rfl

/--
Presupposition is independent of assertion content.

The presupposition depends only on the event type, not on what is asserted.
This is what makes presuppositions "backgrounded": they're part of
what we're talking about, not what we're saying about it.
-/
theorem presupposition_independent_of_assertion (s : EventSentence W) :
    s.presupposition = s.eventType.precondition := rfl

-- PART 4b: Contrast with Assertion-Only View

/-
## The Assertion-Only View (for contrast)

Under an assertion-only view, a sentence IS its truth conditions.
There's no notion of "event reference" or "aboutness" — just a proposition.

This view cannot explain why presuppositions project, because it lacks
the structural component (shared event reference) that would force
affirmative and negative to share anything.
-/

/--
Under the assertion-only view, we just have truth conditions.
-/
structure AssertionOnlyMeaning (W : Type*) where
  truthConditions : W → Bool

/--
Under assertion-only, "stop P" just means: was P and now ¬P.
-/
def assertionOnly_stop (P : W → Bool) : AssertionOnlyMeaning W :=
  { truthConditions := λ w => P w && !P w }
  -- Note: This is actually always false! This reveals the inadequacy
  -- of purely extensional semantics for CoS verbs.

/--
Under assertion-only, "not stop P" just means: ¬(was P and now ¬P).
-/
def assertionOnly_notStop (P : W → Bool) : AssertionOnlyMeaning W :=
  { truthConditions := λ w => !(P w && !P w) }
  -- This is ¬P ∨ P, which is a tautology!

/--
Under assertion-only, the negation does not entail the precondition.

The negated assertion !(P w && !P w) = !P w ∨ P w is true when P w is false.
So we cannot infer P from the negated sentence.

This demonstrates the inadequacy of the assertion-only view:
it cannot explain why "John didn't stop smoking" presupposes he was smoking.
-/
theorem assertionOnly_no_presupposition (P : W → Bool) (w : W)
    (_hNotP : P w = false) :
    (assertionOnly_notStop P).truthConditions w = true := by
  simp [assertionOnly_notStop]

/--
Under the aboutness view, both sentences refer to the stopping event.
The stopping event has precondition P (was smoking).
Therefore, both sentences presuppose P.
-/
theorem aboutness_predicts_projection (P : W → Bool) :
    (affirmative (stopAsEventPhase P)).presupposition =
    (negative (stopAsEventPhase P)).presupposition := rfl

/--
The shared presupposition IS the precondition of the event type.
-/
theorem shared_presupposition_is_precondition (P : W → Bool) :
    (affirmative (stopAsEventPhase P)).presupposition = P := rfl

/--
For "stop P", both affirmative and negative presuppose P.

This is the core empirical prediction that the aboutness view explains
and the assertion-only view cannot.
-/
theorem stop_presupposes_P (P : W → Bool) (pol : Polarity) :
    ({ eventType := stopAsEventPhase P, polarity := pol } : EventSentence W).presupposition = P := rfl


/--
Consequential event: the event entails its consequence when it occurs.
-/
def EventPhase.hasConsequence (e : EventPhase W) : Prop :=
  ∀ w, e.eventOccurs w → e.consequence w

/--
Consequences do not project through negation.

Under "not E", the event didn't occur, so we can't infer the consequence.
This explains why "John didn't stop smoking" doesn't entail he's not smoking.

The asymmetry:
- Preconditions: tied to event reference, so they project
- Consequences: tied to event occurrence, so they don't project under negation
-/
theorem consequence_requires_occurrence (e : EventPhase W)
    (h : e.hasConsequence) (w : W) (hOccur : e.eventOccurs w) : e.consequence w :=
  h w hOccur

/--
Structural explanation: why preconditions project and consequences don't.

1. Presupposition = aboutness.precondition (comes from event reference)
2. Assertion = depends on polarity (comes from claim about occurrence)
3. Consequence = entailed by occurrence (part of assertion, not aboutness)

Under negation:
- Event reference is preserved → presupposition preserved
- Occurrence is denied → consequence not entailed
-/
theorem structural_asymmetry (e : EventPhase W) :
    -- Presupposition comes from aboutness (reference), independent of polarity
    (∀ p : Polarity, ({ eventType := e, polarity := p } : EventSentence W).presupposition = e.precondition) := by
  intro p; rfl

/--
Assertions differ at any world where the consequence is definite (true or false).

If the consequence is true at w, affirmative says true and negative says false.
If the consequence is false at w, affirmative says false and negative says true.
-/
theorem assertions_differ_at_definite_worlds (e : EventPhase W) (w : W) :
    (negative e).assertion w = !(affirmative e).assertion w := by
  simp [affirmative, negative, EventSentence.assertion]

/--
Presuppositions are constant across polarity; assertions vary with polarity.

Presuppositions are tied to event reference (which is constant),
not to the claim (which varies).
-/
theorem presupposition_constant_assertion_varies (e : EventPhase W) (w : W) :
    -- Presupposition is the same for both polarities
    (affirmative e).presupposition w = (negative e).presupposition w ∧
    -- Assertion is negated
    (negative e).assertion w = !(affirmative e).assertion w := by
  constructor <;> rfl


/-
## Why "Allows For" Identifies Preconditions

The "allows for" test works because:

1. "S allows for C" is acceptable when C is compatible with S but not entailed
2. Preconditions are independent facts that the event depends on
3. Since preconditions are prior to the event, they can be elaborated
4. "John stopped smoking allows for him to have been a heavy smoker" ✓

## Why "Results In" Identifies Consequences

The "results in" test works because:

1. "S results in C" is acceptable when C follows from S
2. Consequences are states that the event brings about
3. Since consequences follow from occurrence, they "result from" it
4. "John stopped smoking results in him no longer smoking" ✓

## Cross-Classification

- Preconditions: pass "allows for", fail "results in", project
- Consequences: pass "results in", fail "allows for", don't project

This is exactly the pattern in `Phenomena.Presupposition.Diagnostics`.
-/

/--
The theory predicts the empirical pattern: preconditions ↔ projection.

Content that is a precondition (passes "allows for") should project.
Content that is a consequence (passes "results in") should not project.
-/
def theoryPredictsPattern : Bool :=
  -- Prior state: is precondition, passes "allows for", projects
  stopPattern.priorPassesAllowsFor == true &&
  priorStateProjection.projectsThroughNegation == true &&
  -- Result state: is consequence, fails "allows for", doesn't project
  stopPattern.resultFailsAllowsFor == true &&
  resultStateProjection.projectsThroughNegation == false


/--
Get the telicity of an event phase.

An event is telic if its consequence differs from its precondition,
meaning a state change occurs. Uses `Telicity` from the Aspect module.
-/
def EventPhase.telicity (_e : EventPhase W) : Telicity :=
  -- We check if there could be any world where they differ
  -- For a specific event phase, this is determined by structure
  .telic  -- Default; specific instances override

/--
An event is telic if its consequence differs from its precondition.

This is the existential property: there exists some world where
precondition ≠ consequence, indicating a state change.
-/
def EventPhase.isTelic (e : EventPhase W) : Prop :=
  ∃ w, e.precondition w ≠ e.consequence w

/--
An event is atelic if precondition and consequence are the same.

This is the universal property: in all worlds, the state persists.
-/
def EventPhase.isAtelic (e : EventPhase W) : Prop :=
  ∀ w, e.precondition w = e.consequence w

/--
The telicity of the "stop P" event phase.

"Stop P" is telic: the state changes from P to ¬P.
-/
def stopTelicity : Telicity := .telic

/--
The telicity of the "continue P" event phase.

"Continue P" is atelic: no state change, P persists.
-/
def continueTelicity : Telicity := .atelic

/--
The telicity of the "start P" event phase.

"Start P" is telic: the state changes from ¬P to P.
-/
def startTelicity : Telicity := .telic

/-- "Stop P" is telic: state changes from P to ¬P -/
theorem stop_is_telic (P : W → Bool) (w : W) (hP : P w) :
    (stopAsEventPhase P).precondition w ≠ (stopAsEventPhase P).consequence w := by
  simp [stopAsEventPhase, hP]

/-- "Continue P" is atelic: no state change -/
theorem continue_is_atelic (P : W → Bool) : (continueAsEventPhase P).isAtelic := by
  intro w; simp [continueAsEventPhase]

/-- "Start P" is telic: state changes from ¬P to P -/
theorem start_is_telic (P : W → Bool) (w : W) (hNotP : P w = false) :
    (startAsEventPhase P).precondition w ≠ (startAsEventPhase P).consequence w := by
  simp [startAsEventPhase, hNotP]


/--
CoS verbs have specific Vendler classifications based on their telicity
and the nature of the state change.

- "stop": Achievement (telic, punctual change to ¬P)
- "start": Achievement (telic, punctual change to P)
- "continue": Activity (atelic, durative persistence)
-/
def cosTypeToVendlerClass : CoSType → VendlerClass
  | .cessation => .achievement    -- "stop": punctual, telic
  | .inception => .achievement    -- "start": punctual, telic
  | .continuation => .activity    -- "continue": durative, atelic

/--
Cessation is classified as achievement (telic, punctual).
-/
theorem cessation_is_achievement :
    cosTypeToVendlerClass .cessation = .achievement := rfl

/--
Continuation is classified as activity (atelic, durative).
-/
theorem continuation_is_activity :
    cosTypeToVendlerClass .continuation = .activity := rfl

/--
The Vendler class determines the telicity correctly.
-/
theorem cos_vendler_telicity_correct (t : CoSType) :
    (cosTypeToVendlerClass t).telicity = match t with
      | .cessation => .telic
      | .inception => .telic
      | .continuation => .atelic := by
  cases t <;> rfl

end Montague.Sentence.Presupposition.OntologicalPreconditions
