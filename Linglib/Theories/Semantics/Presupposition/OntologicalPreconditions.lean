/-
# Ontological Preconditions and Projection @cite{roberts-simons-2024}

Presupposition projection based on event structure and ontological dependence.

## Core Claim (@cite{roberts-simons-2024} §2)

The projective contents of three verb classes — CoS predicates, factives, and
predicates with selectional restrictions — are NOT semantically encoded
presuppositions. They are entailments characterizing *ontological preconditions*
of the associated event type. Their projectivity follows from pragmatics
(informativity), not from lexically specified contextual constraints.

## Entailment Classification

Not all entailments are preconditions. Three relations obtain:
- **Precondition**: State that must hold *before* for the event to be possible.
  Projects by pragmatic default. Diagnosed by "allows for" test.
- **Consequence**: State resulting *from* the event. At-issue, doesn't project.
- **Concomitant**: Mereological part or co-occurring state (e.g., "Jane shouted"
  entails "Jane made sound"). At-issue, doesn't project.

## Three Verb Classes

1. **CoS predicates** (stop, start): precondition = prior state
2. **Factives** (know, discover, regret): precondition = complement truth
3. **Selectional restrictions** (kick → has feet): precondition = enabling property

## Diagnostics

Two tests from @cite{roberts-simons-2024} §2.1:
- "ψ, which is part of what allows/allowed for φ" — true iff ψ is precondition
- "If not-ψ, it would not have been possible for [agent] to VP" — counterfactual

-/

import Linglib.Core.Polarity
import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Verb.ChangeOfState.Theory
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect

namespace Semantics.Presupposition.OntologicalPreconditions

open Core.Presupposition
open Semantics.Verb.ChangeOfState
open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs


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

Why do preconditions project through negation? @cite{roberts-simons-2024} argue:

1. Sentences refer to event types (not just assert propositions)
2. Event types have inherent preconditions (ontological requirements)
3. Both "John stopped" and "John didn't stop" refer to the same event type
4. Negation affects the claim about the event, not which event is referenced
5. Therefore, preconditions project: they're tied to the event reference

This contrasts with an assertion-only view where sentences are just truth conditions.
Under assertion-only, there's no structural reason for shared presuppositions.
-/

-- Sentence polarity from Core — .positive = affirmed, .negative = negated
open Core (Polarity)

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
  | .positive => s.eventType.consequence
  | .negative => λ w => !s.eventType.consequence w

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
  { eventType := e, polarity := .positive }

/--
Construct a negative sentence about an event type.
-/
def negative (e : EventPhase W) : EventSentence W :=
  { eventType := e, polarity := .negative }

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

-- ═══════════════════════════════════════════════════════════════════════
-- Contrast with Assertion-Only View
-- ═══════════════════════════════════════════════════════════════════════

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

Without temporal indices, this collapses to `P w ∧ ¬P w` at a single
world — always false. This demonstrates that purely extensional
(single-index) semantics cannot represent CoS verbs: the pre-state
and post-state refer to different temporal indices, and flattening
them into one evaluation point produces a contradiction.
-/
def assertionOnly_stop (P : W → Bool) : AssertionOnlyMeaning W :=
  { truthConditions := λ w => P w && !P w }

/--
Under assertion-only, "not stop P" just means: ¬(was P and now ¬P).
-/
def assertionOnly_notStop (P : W → Bool) : AssertionOnlyMeaning W :=
  { truthConditions := λ w => !(P w && !P w) }
  -- ¬P ∨ P, a tautology

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


/--
The precondition/consequence asymmetry under negation.

Under negation, precondition content survives (via presupposition) but
consequence content is denied (via assertion). This is the structural
basis for why preconditions are the default accommodation target
(@cite{roberts-simons-2024} p. 721): accommodating preconditions is
consistent with both affirming and denying the event, while
accommodating consequences is only consistent with affirmation.
-/
theorem negation_preserves_precondition_denies_consequence
    (e : EventPhase W) (w : W) :
    -- Precondition survives negation (it IS the presupposition)
    (negative e).presupposition w = e.precondition w ∧
    -- Consequence is denied under negation
    (negative e).assertion w = !e.consequence w := by
  constructor <;> rfl

/--
The converse: under affirmation, precondition survives AND consequence
is asserted. Preconditions are consistent with BOTH polarities;
consequences are consistent with only one.
-/
theorem affirmation_preserves_precondition_asserts_consequence
    (e : EventPhase W) (w : W) :
    (affirmative e).presupposition w = e.precondition w ∧
    (affirmative e).assertion w = e.consequence w := by
  constructor <;> rfl


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
Aspectual profile for CoS verb types.

- "stop": Achievement profile (telic, punctual change to ¬P)
- "start": Achievement profile (telic, punctual change to P)
- "continue": Activity profile (atelic, durative persistence)
-/
def cosTypeToAspectualProfile : CoSType → AspectualProfile
  | .cessation => achievementProfile    -- "stop": punctual, telic
  | .inception => achievementProfile    -- "start": punctual, telic
  | .continuation => activityProfile    -- "continue": durative, atelic

/--
CoS verbs have specific Vendler classifications (derived from profile).
-/
def cosTypeToVendlerClass (t : CoSType) : VendlerClass :=
  (cosTypeToAspectualProfile t).toVendlerClass

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

-- ═══════════════════════════════════════════════════════════════════════
-- §5. Entailment Classification
-- ═══════════════════════════════════════════════════════════════════════

/-- Classification of entailment relations between a sentence and its
    implied content (@cite{roberts-simons-2024} §2.1). -/
inductive EntailmentRelation where
  /-- Temporally prior, enables the event. Projects by pragmatic default. -/
  | precondition
  /-- Temporally posterior, results from the event. At-issue. -/
  | consequence
  /-- Mereological part or co-occurring state. At-issue.
      Example: "Jane shouted" entails "Jane made sound" — the sound-making
      is part of the shouting, not a precondition for it. -/
  | concomitant
  deriving DecidableEq, Repr

/-- Only precondition entailments project by pragmatic default. -/
def EntailmentRelation.projects : EntailmentRelation → Bool
  | .precondition => true
  | .consequence  => false
  | .concomitant  => false


-- ═══════════════════════════════════════════════════════════════════════
-- §6. Factive Verbs as Event Phases
-- ═══════════════════════════════════════════════════════════════════════

/-
## Factive Verbs as Event Phases (@cite{roberts-simons-2024} §2, §3.2.2)

R&S extend event phase analysis beyond CoS verbs to factives.
The complement truth of a factive verb is an ontological precondition
of the associated eventuality — not a semantically encoded presupposition.
-/

/-- "Know C" as an event phase: stative, atelic.
    Precondition: C is true. The knowing state cannot exist without its object.
    The state persists without change, so consequence = precondition = C. -/
def knowAsEventPhase (BEL C : W → Bool) : EventPhase W where
  precondition := C
  eventOccurs := λ w => BEL w && C w
  consequence := C  -- stative: no state change

/-- "Discover C" as an event phase: telic, achievement.
    Two preconditions: C is true AND the agent was previously ignorant.
    The discovery transitions from ignorance to knowledge.
    Consequence: C is (still) true and the agent is no longer ignorant. -/
def discoverAsEventPhase (IGNORANT C : W → Bool) : EventPhase W where
  precondition := λ w => C w && IGNORANT w
  eventOccurs := λ w => C w && !IGNORANT w
  consequence := λ w => C w && !IGNORANT w  -- post-state: knows C

/-- "Regret p" as an event phase: emotive factive.
    Precondition: agent believes p (the emotion ontologically
    depends on the belief, not on truth directly).

    @cite{roberts-simons-2024} (p. 731): regret's factivity arises from
    a *pragmatic default to veridicality* — in the absence of an explicit
    claim that the agent is mistaken, emotive attitudes are taken to be
    veridical. The ontological precondition is belief, not truth. -/
def regretAsEventPhase (BEL : W → Bool) : EventPhase W where
  precondition := BEL
  eventOccurs := BEL
  consequence := BEL

/-- Know is atelic: no state change (precondition = consequence). -/
theorem know_is_atelic (BEL C : W → Bool) : (knowAsEventPhase BEL C).isAtelic := by
  intro w; simp [knowAsEventPhase]

/-- Discover is telic: state change from ignorant to knowing. -/
theorem discover_is_telic (IGNORANT C : W → Bool) (w : W)
    (hC : C w = true) (hIgn : IGNORANT w = true) :
    (discoverAsEventPhase IGNORANT C).precondition w ≠
    (discoverAsEventPhase IGNORANT C).consequence w := by
  simp [discoverAsEventPhase, hC, hIgn]

/-- Both know and discover have C as (part of) their precondition.
    This is the shared factivity: complement truth is ontologically required. -/
theorem factive_precondition_entails_complement (IGNORANT C : W → Bool) (w : W) :
    (discoverAsEventPhase IGNORANT C).precondition w = true → C w = true := by
  simp [discoverAsEventPhase]; intro h _; exact h

/-- Discover's precondition additionally requires prior ignorance.
    This extra precondition (ignorance of C) explains why discover
    has weaker projection than know in conditional antecedents:
    in "If I discover p", the speaker's ignorance of p is salient,
    suppressing projection of C (@cite{roberts-simons-2024} §3.2.2). -/
theorem discover_precondition_requires_ignorance (IGNORANT C : W → Bool) (w : W) :
    (discoverAsEventPhase IGNORANT C).precondition w = true → IGNORANT w = true := by
  simp [discoverAsEventPhase]

/-- Continue has a precondition (prior activity) but involves NO state change.
    @cite{roberts-simons-2024} (p. 734): "continue V-ing is atelic, without a
    pre-state" in the CoS sense. The `CoSType.continuation` classification is
    a convenience; the key structural fact is `isAtelic`. -/
theorem continue_has_precondition_without_state_change (P : W → Bool) :
    (continueAsEventPhase P).precondition = P ∧
    (continueAsEventPhase P).isAtelic := by
  constructor
  · rfl
  · intro w; simp [continueAsEventPhase]


-- ═══════════════════════════════════════════════════════════════════════
-- §7. Selectional Restrictions as Preconditions
-- ═══════════════════════════════════════════════════════════════════════

/-
## Selectional Restrictions (@cite{roberts-simons-2024} §2.1)

Selectional restrictions are ontological preconditions of the same kind
as factive and CoS projections. "The robot kicked the tree" implies
"the robot has feet" — this is a precondition, confirmed by both
diagnostics:

(13a) "The robot has feet, which is part of what allowed for the robot
       to kick the tree." (T)
(14a) "If the robot did not have feet, it would not have been possible
       for the robot to kick the tree." (T — counterfactual)

This unifies selectional restrictions with the other two verb classes
under a single mechanism: ontological precondition → pragmatic projection.
-/

/-- A selectional restriction as an event phase.
    The `requirement` is an ontological precondition of the event. -/
def selectionalEventPhase (requirement event : W → Bool) : EventPhase W where
  precondition := requirement
  eventOccurs := event
  consequence := event

/-- Selectional restrictions are well-formed: the event entails the requirement. -/
theorem selectional_wellFormed (requirement event : W → Bool)
    (h : ∀ w, event w = true → requirement w = true) :
    (selectionalEventPhase requirement event).wellFormed := h

/-- Selectional restrictions project through negation (same aboutness mechanism). -/
theorem selectional_projects (requirement event : W → Bool) :
    (affirmative (selectionalEventPhase requirement event)).presupposition =
    (negative (selectionalEventPhase requirement event)).presupposition := rfl


-- ═══════════════════════════════════════════════════════════════════════
-- §8. Pragmatic Suppression Conditions
-- ═══════════════════════════════════════════════════════════════════════

/-
## Suppression Conditions (@cite{roberts-simons-2024} §3.2.1)

Projection of preconditions is a pragmatic *default*, not an invariant.
Three contexts suppress projection — in each, pragmatic reasoning makes
it implausible that the speaker presumes the precondition true.
-/

/-- Conditions under which projection of a precondition is suppressed.
    When any of these obtains, the hearer does not accommodate the
    precondition into the global context. -/
inductive SuppressionCondition where
  /-- Interlocutors know or believe the precondition is false or controversial.
      Example: discussing politics with someone who denies the premise.
      (@cite{roberts-simons-2024} ex. 23) -/
  | preconditionKnownFalse
  /-- Evidence that the speaker does not believe the precondition.
      Example: "I doubt that. Mary would divorce him if she discovered
      he was drinking." — speaker explicitly doubts the drinking.
      (@cite{roberts-simons-2024} ex. 24) -/
  | speakerNonCommitment
  /-- The precondition is at-issue (currently under discussion).
      Example: "Is there a decision on Jane's tenure case?" "She isn't
      aware that there's been a decision." — decision existence is QUD.
      (@cite{roberts-simons-2024} ex. 25) -/
  | preconditionAtIssue
  deriving DecidableEq, Repr

/-- When suppression applies, precondition content is merely locally entailed,
    not globally accommodated. The content is still an entailment of the
    trigger — it simply isn't taken to be part of the speaker's presumptions. -/
def SuppressionCondition.globalProjection : SuppressionCondition → Bool
  | _ => false

end Semantics.Presupposition.OntologicalPreconditions
