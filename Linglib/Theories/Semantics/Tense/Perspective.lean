import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Core.DiscourseRole
import Linglib.Core.Context
import Linglib.Theories.Morphology.Tense

/-!
# Tense and Participant Perspective (Lakoff 1970)

Lakoff (1970) "Tense and Its Relation to Participants" argues that tense
selection is sensitive to speaker/hearer epistemic states, not just temporal
ordering. The chipmunk *IS* still there, but the speaker uses past tense
because the event is no longer psychologically **salient**. Likewise, present
tense can survive under a past-tense matrix verb when the embedded content is
**novel** to the hearer ("He discovered that the boy has blue eyes").

This module extends `EvidentialFrame` with two orthogonal Boolean participant
dimensions — `speakerSalience` and `hearerNovelty` — and defines Lakoff's
five key predicates on this enriched structure.

## Relationship to Cumming (2026)

Cumming's `EvidentialFrame` adds acquisition time A to Reichenbach's (S, R, E),
capturing the constraint that nonfuture evidence is *downstream* of the event.
Lakoff's observations are orthogonal: "false past" arises even when evidence IS
downstream (the chipmunk is still there = T ≤ A holds), because the event has
lost psychological salience. `TensePerspective` inherits the full (S, R, E, A)
frame and adds the participant-psychological layer on top.

## References

- Lakoff, R. (1970). Tense and its relation to participants. *Language* 46(4).
- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
-/

namespace Semantics.Tense.Perspective

open Semantics.Tense.Evidential
open Semantics.Tense

-- ════════════════════════════════════════════════════
-- § 1. Tense Perspective Frame
-- ════════════════════════════════════════════════════

/-- Lakoff's participant-sensitive tense frame. Extends `EvidentialFrame`
    (which already extends `ReichenbachFrame`) with two psychological dimensions:

    - `speakerSalience`: is the event psychologically salient to the speaker
      at speech time S?
    - `hearerNovelty`: is the propositional content new to the hearer? -/
structure TensePerspective (Time : Type*) extends EvidentialFrame Time where
  /-- Is the event psychologically salient to the speaker at S? -/
  speakerSalience : Bool
  /-- Is the propositional content new to the hearer? -/
  hearerNovelty : Bool

-- ════════════════════════════════════════════════════
-- § 2. Lakoff Predicates
-- ════════════════════════════════════════════════════

/-- **False past** (Lakoff §1): past tense applied to a present-time event
    because the speaker no longer finds it salient.

    Example: "The animal you saw WAS a chipmunk" (it still IS one).
    The event time equals speech time, but salience is absent. -/
def falsePast (f : TensePerspective ℤ) : Prop :=
  f.eventTime = f.speechTime ∧ ¬(f.speakerSalience = true)

/-- **False future** (Lakoff §1): future tense applied to a present-time event
    because the speaker treats it as not yet salient.

    Example: "That thing WILL be a chipmunk" (it already IS one).
    Same licensing condition as false past — the divergence is in surface
    morphology (a Fragment-level concern). -/
def falseFuture (f : TensePerspective ℤ) : Prop :=
  f.eventTime = f.speechTime ∧ ¬(f.speakerSalience = true)

/-- **Novel-information present** (Lakoff §2): present tense survives under a
    past-tense matrix verb because the embedded content is new to the hearer.

    Example: "He discovered that the boy HAS blue eyes."
    The event time equals speech time and the content is novel. -/
def novelInfoPresent (f : TensePerspective ℤ) : Prop :=
  f.hearerNovelty = true ∧ f.eventTime = f.speechTime

/-- **Perfect requires salience** (Lakoff §4): the present perfect is
    infelicitous when the event lacks current relevance to the speaker.

    Example: *"Einstein has visited Princeton" — infelicitous because
    Einstein is dead and the event has no current relevance. -/
def perfectRequiresSalience (f : TensePerspective ℤ) : Prop :=
  f.speakerSalience = true

/-- **Will-deletion** (Lakoff §5): future-time events can appear in present
    tense (deleting *will*) when the speaker treats them as salient and
    controlled/scheduled.

    Example: "The meeting starts at 3" (= will start, but scheduled).
    The event is future (S < T) but salient. -/
def willDeletion (f : TensePerspective ℤ) : Prop :=
  f.speechTime < f.eventTime ∧ f.speakerSalience = true

-- ════════════════════════════════════════════════════
-- § 3. True vs False Tense Classification
-- ════════════════════════════════════════════════════

open Core.Morphology.Tense in

/-- Lakoff's central classification: a tense use is **true** when the
    grammatical tense matches the temporal relation, **false** when there
    is a mismatch (tense encodes psychological perspective instead). -/
inductive TenseUse where
  | trueTense   -- grammatical tense matches temporal relation
  | falseTense  -- grammatical tense diverges from temporal relation
  deriving DecidableEq, Repr, BEq

/-- Classify a tense use based on whether the grammatical tense matches
    the temporal reality. A `GramTense.past` with `eventTime = speechTime`
    is false (the event is present-time despite past morphology). -/
def classifyUse (gramTense : GramTense) (f : TensePerspective ℤ) : TenseUse :=
  match gramTense with
  | .past    => if f.eventTime < f.speechTime then .trueTense else .falseTense
  | .present => if f.eventTime = f.speechTime then .trueTense else .falseTense
  | .future  => if f.speechTime < f.eventTime then .trueTense else .falseTense

open Core.Morphology.Tense in

/-- **Periphrastic forms block false tense** (Lakoff §1, ex. 8a vs 9a):
    if the tense use is false and the form is periphrastic, the result is
    unacceptable. Only synthetic forms can carry false-tense interpretations.

    This is stated as: false tense requires synthetic form. -/
def falseTenseRequiresSynthetic (use : TenseUse) (form : TenseFormType) : Bool :=
  match use with
  | .trueTense  => true   -- true tense is fine with any form
  | .falseTense => form == .synthetic  -- false tense needs synthetic

-- ════════════════════════════════════════════════════
-- § 4. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- When `falsePast` holds, the UP present-tense constraint (T = S) is satisfied.
    The event IS at speech time, despite the past surface tense — the mismatch
    is purely psychological (salience), not temporal. -/
theorem false_past_satisfies_up_present (f : TensePerspective ℤ)
    (h : falsePast f) :
    UPCondition.present.toConstraint f.toEvidentialFrame := by
  exact h.1

/-- Speaker salience strictly exceeds bare downstream evidence: when both hold,
    we have the conjunction. This captures Lakoff's insight that salience is an
    additional dimension beyond Cumming's evidential constraint. -/
theorem salience_with_downstream (f : TensePerspective ℤ)
    (h_sal : f.speakerSalience = true)
    (h_down : downstreamEvidence f.toEvidentialFrame) :
    f.speakerSalience = true ∧ downstreamEvidence f.toEvidentialFrame :=
  ⟨h_sal, h_down⟩

end Semantics.Tense.Perspective
