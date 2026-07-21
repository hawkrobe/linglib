import Mathlib.Tactic.TypeStar
import Linglib.Features.Polarity

/-!
# Ontological preconditions and projection

[roberts-simons-2024]'s event-phase account of non-anaphoric presupposition:
projective contents are entailments characterizing *ontological
preconditions* of the event type a sentence is about, and project because
affirmation and negation share that event reference — not because they are
semantically encoded presuppositions.

## Main declarations

* `EventPhase` — an event decomposed into precondition, occurrence, and
  consequence, with `wellFormed` (occurrence entails precondition) and the
  telicity predicates `isTelic`/`isAtelic`.
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

namespace Semantics.Presupposition.OntologicalPreconditions

open Features (Polarity)

variable {W : Type*}

/-- An event decomposed into temporal phases: the state that must hold
    *before* for the event to be possible, the occurrence itself, and the
    state that holds *after*. -/
structure EventPhase (W : Type*) where
  /-- Precondition: must hold before the event for it to be possible -/
  precondition : W → Prop
  /-- The event actually occurs -/
  eventOccurs : W → Prop
  /-- Consequence: holds after the event (result state) -/
  consequence : W → Prop

/-- Well-formed event: the occurrence entails its precondition — the
    ontological constraint (you can't stop smoking unless you were smoking). -/
def EventPhase.wellFormed (e : EventPhase W) : Prop :=
  ∀ w, e.eventOccurs w → e.precondition w

/-- An event is telic if its consequence differs from its precondition at
    some world (a state change). -/
def EventPhase.isTelic (e : EventPhase W) : Prop :=
  ∃ w, e.precondition w ≠ e.consequence w

/-- An event is atelic if precondition and consequence coincide everywhere
    (the state persists). -/
def EventPhase.isAtelic (e : EventPhase W) : Prop :=
  ∀ w, e.precondition w = e.consequence w

/-! ### The aboutness mechanism

Sentences refer to event types; event types have inherent preconditions;
and "John stopped" and "John didn't stop" refer to the *same* event type —
negation affects the claim about the event, not which event is referenced.
Preconditions therefore project, because they are tied to event reference
rather than to the polarity-dependent claim. -/

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

end Semantics.Presupposition.OntologicalPreconditions
