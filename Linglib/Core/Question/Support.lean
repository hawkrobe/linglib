import Mathlib.Logic.Basic
import Mathlib.Data.List.Basic

/-!
# Question Support — cross-tradition `s ⊨ Q` interface

A theory-neutral typeclass for the relation "state `s` supports / resolves
question `Q`". The literature calls this *support* in inquisitive semantics
(`s ⊨ Q`); the @cite{ginzburg-2012} KOS framework calls it *answerhood*
(a fact resolves a question); decision-theoretic and TTR variants give it
yet other names. This file fixes the shared interface.

## Why a typeclass

Different frameworks bring different mathematical structure to questions
(inquisitive issues, partitions, structured meanings, TTR records,
Austinian propositions, decision problems). What they share is a binary
"this state settles this question" relation. By exposing only that relation
through a typeclass, downstream files (KOS dialogue rules, RSA decision
utilities, anaphora resolution) can be written once against `Support` and
specialise to whichever question representation a study actually uses.

## Design

* `supports : State → Question → Prop` — Prop-valued, mathlib-shaped.
  Decidability is a separate concern, recovered via `[DecidableRel]`-style
  instances where the underlying representation supports it.
* Scoped notation `s ⊨ q` for `Support.supports s q`. Scoped to
  `Core.Question` so it can coexist with the inquisitive `s ⊨ p` from
  `Core.Question.Basic` (which is its eventual home — once that namespace is
  consolidated, this notation will simply *be* the canonical one).
* `allResolved` lifts to lists for direct use by KOS QUD-downdate.

## Relation to existing infrastructure

* `Pragmatics.Dialogue.KOS.Answerhood` — the legacy Bool-valued typeclass
  used by the KOS rules. A bridge instance there will provide a
  `Core.Question.Support` instance from any `Answerhood` instance, so this
  file can be adopted incrementally without breaking the KOS consumers.
* `Core.Question.Answerhood` — concrete mention-some/mention-all predicates
  over `Question W`. Separate concept (specific answerhood notions), not a
  typeclass.
* `Semantics.Questions.Support` — IKW (@cite{ippolito-kiss-williams-2025})
  evidential SUPPORT: doxastic + probabilistic. A specialised theory of
  *what* supports a question; this file is the bare relation.
-/

namespace Core.Question

/-- The state `s` supports / resolves the question `q`.

In inquisitive semantics this is `s ⊨ Q` (Ciardelli-Groenendijk-Roelofsen);
in @cite{ginzburg-2012} this is "FACTS contextually entail an answer to q".
The interface is intentionally minimal: it says nothing about whether the
support is exhaustive, mention-some, partial, or probabilistic — those
notions specialise it. -/
class Support (State Question : Type*) where
  /-- The support / resolution relation. -/
  supports : State → Question → Prop

@[inherit_doc] scoped notation:50 s " ⊨ " q => Support.supports s q

namespace Support

variable {State Question : Type*}

/-- Every question in the list is supported by some state in the list.

Used by KOS QUD-downdate: a QUD entry is removed once any FACT supports it. -/
def allResolved [Support State Question]
    (states : List State) (questions : List Question) : Prop :=
  ∀ q ∈ questions, ∃ s ∈ states, s ⊨ q

instance allResolved.instDecidable
    [Support State Question]
    [DecidableRel (Support.supports : State → Question → Prop)]
    (states : List State) (questions : List Question) :
    Decidable (allResolved states questions) := by
  unfold allResolved
  infer_instance

end Support

end Core.Question
