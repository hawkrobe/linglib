import Linglib.Semantics.Events.Phase
import Linglib.Features.Polarity

/-!
# The aboutness account of projection

[roberts-simons-2024]'s mechanism for non-anaphoric presupposition:
sentences refer to event types (`EventPhase`); event types have inherent
ontological preconditions; and "John stopped" and "John didn't stop" refer
to the *same* event type — negation affects the claim about the event, not
which event is referenced. Preconditions therefore project, because they
are tied to event reference rather than to the polarity-dependent claim.

## Main declarations

* `EventSentence` — a sentence as event reference (`aboutness`) plus a
  polarity-dependent claim (`assertion`); its `presupposition` is the
  precondition of the referenced event type, so projection through negation
  (`presupposition_projects`) holds by construction while assertions flip
  (`assertion_differs`).
* `EntailmentRelation` — precondition vs consequence vs concomitant; only
  preconditions project by pragmatic default (`projects`).

The paper's verb-class instances (CoS predicates, factives, selectional
restrictions), aspectual classification, and suppression conditions live in
`Studies/RobertsSimons2024.lean`.
-/

namespace Semantics.Presupposition.Aboutness

open Features (Polarity)

variable {W : Type*}

/-- A sentence that refers to an event type and makes a polarity-dependent
    claim about it. -/
structure EventSentence (W : Type*) where
  /-- The event type this sentence is about -/
  eventType : EventPhase W
  /-- The polarity of the claim -/
  polarity : Polarity

/-- The aboutness of a sentence: the event type it refers to, independent
    of polarity. -/
def EventSentence.aboutness (s : EventSentence W) : EventPhase W :=
  s.eventType

/-- The claim made: affirmed sentences assert the consequence obtains,
    negated ones that it doesn't. -/
def EventSentence.assertion (s : EventSentence W) : W → Prop :=
  match s.polarity with
  | .positive => s.eventType.consequence
  | .negative => λ w => ¬ s.eventType.consequence w

/-- The presupposition comes from aboutness, not from the assertion: it is
    the precondition of the referenced event type. -/
def EventSentence.presupposition (s : EventSentence W) : W → Prop :=
  s.aboutness.precondition

/-- An affirmative sentence about an event type. -/
def affirmative (e : EventPhase W) : EventSentence W :=
  { eventType := e, polarity := .positive }

/-- A negative sentence about an event type. -/
def negative (e : EventPhase W) : EventSentence W :=
  { eventType := e, polarity := .negative }

/-- Presuppositions project through negation: derived from aboutness, which
    affirmation and negation share. -/
theorem presupposition_projects (e : EventPhase W) :
    (affirmative e).presupposition = (negative e).presupposition := rfl

/-- Assertions flip with polarity while presuppositions stay constant. -/
theorem assertion_differs (e : EventPhase W) (w : W) :
    (negative e).assertion w ↔ ¬ (affirmative e).assertion w := Iff.rfl

/-! ### Entailment classification -/

/-- Classification of entailment relations between a sentence and its
    implied content: only preconditions project ([roberts-simons-2024] §2.1
    diagnostics: "ψ, which is part of what allowed for φ" and the
    counterfactual "if not-ψ, φ would not have been possible"). -/
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

end Semantics.Presupposition.Aboutness
