import Linglib.Semantics.Events.Phase
import Linglib.Features.Polarity

/-!
# The precondition account of non-anaphoric presupposition

[roberts-simons-2024]'s characterization: the projective contents of CoS
predicates, factives, and selectional restrictions are entailments
characterizing *ontological preconditions* of the associated event type
(`EventPhase`), not semantically encoded presuppositions. Projection is
pragmatic — *projection in service of informativity*: accommodating
preconditions is the safer default because preconditions are consistent
with both affirming and denying the event, while consequences hold only if
it occurred. The structural basis is that affirmation and negation share
event reference: `EventSentence` separates what a sentence is about (its
event type) from the polarity-dependent claim, so the precondition is
invariant across polarity (`presupposition_projects`) while assertions flip
(`assertion_differs`).

## Main declarations

* `EventSentence` — event reference plus a polarity-dependent claim;
  `presupposition` is the precondition of the referenced event type.
* `EntailmentRelation` — precondition vs consequence vs concomitant
  ([roberts-simons-2024] §2.1 diagnostics); only preconditions project by
  pragmatic default (`projects`).

The paper's verb-class instances, aspectual classification, and suppression
conditions live in `Studies/RobertsSimons2024.lean`; the RSA models it
cites as proof-of-concept are `Studies/QingGoodmanLassiter2016.lean` and
`Studies/Warstadt2022.lean`.
-/

namespace Semantics.Presupposition.Preconditions

open Features (Polarity)

variable {W : Type*}

/-- A sentence that refers to an event type and makes a polarity-dependent
    claim about it. -/
structure EventSentence (W : Type*) where
  /-- The event type this sentence is about -/
  eventType : EventPhase W
  /-- The polarity of the claim -/
  polarity : Polarity

/-- The claim made: affirmed sentences assert the consequence obtains,
    negated ones that it doesn't. -/
def EventSentence.assertion (s : EventSentence W) : W → Prop :=
  match s.polarity with
  | .positive => s.eventType.consequence
  | .negative => λ w => ¬ s.eventType.consequence w

/-- The presupposition is the precondition of the referenced event type —
    tied to event reference, not to the claim being made. -/
def EventSentence.presupposition (s : EventSentence W) : W → Prop :=
  s.eventType.precondition

/-- An affirmative sentence about an event type. -/
def affirmative (e : EventPhase W) : EventSentence W :=
  { eventType := e, polarity := .positive }

/-- A negative sentence about an event type. -/
def negative (e : EventPhase W) : EventSentence W :=
  { eventType := e, polarity := .negative }

/-- Presuppositions project through negation: the precondition is derived
    from event reference, which affirmation and negation share. -/
theorem presupposition_projects (e : EventPhase W) :
    (affirmative e).presupposition = (negative e).presupposition := rfl

/-- Assertions flip with polarity while presuppositions stay constant. -/
theorem assertion_differs (e : EventPhase W) (w : W) :
    (negative e).assertion w ↔ ¬ (affirmative e).assertion w := Iff.rfl

/-! ### Entailment classification -/

/-- Classification of entailment relations between a sentence and its
    implied content: only preconditions project ([roberts-simons-2024] §2.1
    diagnostics: "ψ, which is part of what allowed for φ" and the
    counterfactual "if not-ψ, it would not have been possible to VP"). -/
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

end Semantics.Presupposition.Preconditions
