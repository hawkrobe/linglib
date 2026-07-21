import Linglib.Semantics.Events.Phase
import Linglib.Semantics.Presupposition.Basic

/-!
# The precondition account of non-anaphoric presupposition

[roberts-simons-2024]'s characterization: the projective contents of CoS
predicates, factives, and selectional restrictions are entailments
characterizing *ontological preconditions* of the associated event type
(`Event.Phase`), not semantically encoded presuppositions. Projection is
pragmatic — *projection in service of informativity*: accommodating
preconditions is the safer default because preconditions are consistent
with both affirming and denying the event, while consequences hold only if
it occurred.

The account is a hom `Event.Phase.toPartialProp`: an event sentence
presupposes the event type's precondition and asserts its result state.
Negating the sentence is `PartialProp.neg` — internal negation, a hole —
so preconditions project through negation by `PartialProp.neg_presup`:
negation affects the claim about the event, not which event type is
referenced.

## Main declarations

* `Event.Phase.toPartialProp` — the denotation hom; `toPartialProp_neg_presup`
  is projection through negation.
* `EntailmentRelation` — precondition vs consequence vs concomitant
  ([roberts-simons-2024] §2.1 diagnostics); only preconditions project by
  pragmatic default (`projects`).

The paper's verb-class instances, aspectual classification, and suppression
conditions live in `Studies/RobertsSimons2024.lean`; the RSA models it
cites as proof-of-concept are `Studies/QingGoodmanLassiter2016.lean` and
`Studies/Warstadt2022.lean`.
-/

namespace Event.Phase

open Semantics.Presupposition

variable {W : Type*}

/-- The [roberts-simons-2024] denotation of an event sentence: presuppose
    the event type's ontological precondition, assert its result state.
    The negated sentence is `(e.toPartialProp).neg`. -/
def toPartialProp (e : Event.Phase W) : PartialProp W where
  presup := e.precondition
  assertion := e.consequence

@[simp] theorem toPartialProp_presup (e : Event.Phase W) :
    e.toPartialProp.presup = e.precondition := rfl

@[simp] theorem toPartialProp_assertion (e : Event.Phase W) :
    e.toPartialProp.assertion = e.consequence := rfl

/-- Preconditions project through negation: internal negation is a hole
    (`PartialProp.neg_presup`), and the precondition is carried by the
    presupposition component. -/
theorem toPartialProp_neg_presup (e : Event.Phase W) :
    e.toPartialProp.neg.presup = e.precondition := rfl

end Event.Phase

namespace Semantics.Presupposition.Preconditions

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
