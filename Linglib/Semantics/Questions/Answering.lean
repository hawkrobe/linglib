module

public import Linglib.Semantics.Polarity.Basic

/-!
# Answering yes–no questions

This file formalizes the syntax of answers to yes–no questions of [holmberg-2016]. A yes–no
question contains a polarity head merged unvalued, and an answer merges a focused valued
polarity feature, spelled out by an answer particle, with the PolP inherited from the question.
An `AnswerParticle` carries the value it assigns, [+Pol] or [−Pol], and possibly REV, the
feature of a polarity-reversing particle such as Swedish *jo*, which eliminates the negation in
the answer. A `PolP` records where the question's negation sits relative to the polarity head,
and `PolP.answer` computes the polarity of the alternative the answer confirms, relative to the
question's positive alternative, or `none` for an ill-formed answer; the action of
`Polarity` on propositions turns that polarity into the alternative itself.

A negation out of the polarity head's reach, such as a low, VP-internal one, leaves the particle
to value the head, and the value composes with the negation: an affirmative particle confirms
the negative alternative, a negative one is a double negation. A middle negation values the head
itself: a negative particle agrees with it and a plain affirmative clashes with it. These are
the truth-based and the polarity-based systems for answering negative questions
(`AnsweringSystem`, `NegationHeight.predictedSystem`).

## Implementation notes

* What decides the system is whether the negation can value the polarity head
  (`PolP.ValuedByNegation`); the height of the negation matters only through that
  ([holmberg-2016] on Thai, whose negation cannot value the head from inside the complement of
  the question particle). Heights classify constructions, not languages: English *not* is read
  low by some speakers and middle by others, and *-n't* in positive-bias questions is high.
* REV needs a negation in the answer to eliminate, so a reversing particle is ill formed after a
  neutral or a positive-bias question. Colloquial Swedish, where *jo* can confirm the positive
  alternative of any yes–no question ([holmberg-2016], footnote to the section on positive and
  negative bias), is not modelled.

## References

* [holmberg-2016]
-/

@[expose] public section

namespace Question

/-- The two systems for answering negative yes–no questions ([holmberg-2016]), told apart by the
particle that confirms the negative alternative of *Does John not drink coffee?*. -/
inductive AnsweringSystem where
  /-- The affirmative particle confirms the negative alternative (Japanese, Cantonese, Thai). -/
  | truthBased
  /-- The negative particle confirms the negative alternative (Swedish, Finnish, English with
  the middle reading of *not*). -/
  | polarityBased
  deriving DecidableEq, Repr

/-- An answer particle: the value it assigns to the polarity head, and whether it carries REV,
the feature of a polarity-reversing particle that eliminates a negation in the answer
([holmberg-2016]'s `[jo, +Pol, REV]`). Answer particles are pro-sentential, deliberately outside
the host-associated `Syntax/Category/Particle` core. -/
structure AnswerParticle where
  /-- Citation form. -/
  form : String
  /-- The value assigned to [±Pol]. -/
  assigns : Polarity
  /-- Whether the particle carries REV. -/
  reverses : Bool := false
  deriving DecidableEq, Repr

/-- Structural height of a sentential negation relative to the polarity head. The height
classifies constructions, not languages: English *not* is read low by some speakers and middle
by others, and low by all after an adverb; *-n't* in positive-bias questions is high. -/
inductive NegationHeight where
  /-- Negation below the reach of the polarity head, VP-internal (English *not* on its low
  reading). -/
  | low
  /-- Negation in a local c-command relation to the polarity head (Swedish, Finnish, English
  *not* on its middle reading). -/
  | middle
  /-- Negation above the polarity head, in the C-domain (English *-n't* in positive-bias
  questions). -/
  | high
  deriving DecidableEq, Repr

/-- The PolP an answer inherits from a yes–no question: the height of the question's negation
(`none` for a neutral question), and whether an adverb scoping over a middle negation keeps it
from valuing the polarity head. -/
structure PolP where
  /-- The height of the negation, if any. -/
  negation : Option NegationHeight := none
  /-- An adverb scoping over a middle negation, as in Swedish *nångång inte*. -/
  intervener : Bool := false
  deriving DecidableEq, Repr

namespace PolP

variable (q : PolP)

/-- The negation sits inside the PolP, so that both alternatives of the question contain it. -/
def NegationInside : Prop := q.negation = some .low ∨ q.negation = some .middle

instance : Decidable q.NegationInside := inferInstanceAs (Decidable (_ ∨ _))

/-- The polarity of the question's primary alternative relative to its positive alternative:
negative when the negation is inside the PolP. -/
def polarity : Polarity := if q.NegationInside then .negative else .positive

/-- The negation values the polarity head: a middle negation not screened off by an adverb. -/
def ValuedByNegation : Prop := q.negation = some .middle ∧ q.intervener = false

instance : Decidable q.ValuedByNegation := inferInstanceAs (Decidable (_ ∧ _))

/-- The polarity of the alternative an answer particle confirms, relative to the positive
alternative, or `none` when the answer is ill formed. A reversing particle eliminates the
negation inside the PolP and values the head, and is ill formed without one. Otherwise, if the
negation values the head, a negative particle agrees with it and an affirmative one clashes with
it; if not, the particle values the head, composing with a negation inside the PolP. -/
def answer (a : AnswerParticle) : Option Polarity :=
  if a.reverses then
    if q.NegationInside then some a.assigns else none
  else if q.ValuedByNegation then
    if a.assigns = .negative then some .negative else none
  else some (a.assigns * q.polarity)

variable {q} {a : AnswerParticle}

/-- A reversing particle eliminates the negation inside the PolP and values the head. -/
theorem answer_of_reverses (hr : a.reverses = true) (h : q.NegationInside) :
    q.answer a = some a.assigns := by
  simp [answer, hr, h]

/-- A reversing particle has no negation to eliminate outside a negative-bias question. -/
theorem answer_eq_none_of_reverses (hr : a.reverses = true) (h : ¬ q.NegationInside) :
    q.answer a = none := by
  simp [answer, hr, h]

/-- A negation valuing the head: a plain negative particle agrees with it, confirming the
negative alternative, and a plain affirmative one clashes with it. -/
theorem answer_of_valuedByNegation (hr : a.reverses = false) (h : q.ValuedByNegation) :
    q.answer a = if a.assigns = .negative then some .negative else none := by
  simp [answer, hr, h]

/-- Without a negation valuing the head, a plain particle values it and composes with the
polarity of the primary alternative. -/
theorem answer_of_not_valuedByNegation (hr : a.reverses = false) (h : ¬ q.ValuedByNegation) :
    q.answer a = some (a.assigns * q.polarity) := by
  simp [answer, hr, h]

/-- A negation inside the PolP that does not value the head admits every particle, so a
truth-based configuration has no need of a reversing particle. -/
theorem answer_ne_none_of_negationInside (hi : q.NegationInside) (h : ¬ q.ValuedByNegation) :
    q.answer a ≠ none := by
  cases hr : a.reverses
  · simp [answer_of_not_valuedByNegation hr h]
  · simp [answer_of_reverses hr hi]

end PolP

/-- The negative-bias question whose negation has height `n`, with no adverb screening it. -/
def NegationHeight.toPolP (n : NegationHeight) : PolP := ⟨some n, false⟩

/-- The answering system a negative-bias question exhibits at each height of its negation:
truth-based for the low negation, polarity-based otherwise. -/
def NegationHeight.predictedSystem : NegationHeight → AnsweringSystem
  | .low    => .truthBased
  | .middle => .polarityBased
  | .high   => .polarityBased

/-- The classification is read off the mechanism: a height is truth-based iff a plain
affirmative particle confirms the negative alternative of the question with that negation. -/
theorem NegationHeight.predictedSystem_eq_truthBased_iff (n : NegationHeight)
    {a : AnswerParticle} (ha : a.assigns = .positive) (hr : a.reverses = false) :
    n.predictedSystem = .truthBased ↔ n.toPolP.answer a = some .negative := by
  cases n <;> simp [predictedSystem, toPolP, PolP.answer, PolP.ValuedByNegation, PolP.polarity,
    PolP.NegationInside, ha, hr]

end Question
