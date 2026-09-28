module

public import Linglib.Discourse.Response
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Questions.Hamblin

/-!
# Polar interrogatives and their answers

This file formalizes the syntax of yes–no questions and their answers of [holmberg-2016]. A
`PolarInterrogative` is a sentence radical, its positive alternative, with a `ClauseNegation`,
the negation of the clause, if any, with its height relative to the polarity head. Its primary
alternative is the radical under the polarity the negation gives it, and it denotes the polar
question of that alternative; a negative interrogative and its positive counterpart denote the
same question, differing only in which alternative is primary
(`PolarInterrogative.denote_eq_polar_radical`).

The polarity head is merged unvalued, and a short answer merges a focused valued polarity
feature, spelled out by an answer particle, with the clause inherited from the question,
normally elided. An `AnswerFeature` is that feature: a valued [+Pol] or [−Pol], or the
affirmative [+Pol, REV] of a polarity-reversing particle such as Swedish *jo*, which eliminates
the negation in the answer. Given the negation of the clause the answer inherits,
`AnswerFeature.answer` computes the polarity
of the alternative the answer confirms, relative to the question's positive alternative, or
`none` for an ill-formed answer; the action of `Polarity` on propositions turns that polarity
into the alternative itself.

A negation out of the polarity head's reach, such as a low, VP-internal one, leaves the particle
to value the head, and the value composes with the negation: an affirmative particle confirms
the negative alternative, a negative one is a double negation. A middle negation values the head
itself: a negative particle agrees with it and a plain affirmative clashes with it. These are
the truth-based and the polarity-based systems for answering negative questions
(`AnsweringSystem`, `NegationHeight.predictedSystem`).

The answers a feature gives to the questions whose negations a language allows form a set of
`Discourse.Response`s (`AnswerFeature.responses`), the carrier of the polarity features of
[farkas-bruce-2010], to whom [holmberg-2016] credits REV: a reversing feature gives exactly the
[reverse, +] answers (`AnswerFeature.responses_reversing`).

## Implementation notes

* What decides the system is whether the negation can value the polarity head
  (`ClauseNegation.ValuesHead`); the height of the negation matters only through that
  ([holmberg-2016] on Thai, whose negation cannot value the head from inside the complement of
  the question particle). Heights classify constructions, not languages: English *not* is read
  low by some speakers and middle by others, and *-n't* in positive-bias questions is high.
* REV needs a negation in the answer to eliminate, so a reversing particle is ill formed after a
  neutral or a positive-bias question. Colloquial Swedish, where *jo* can confirm the positive
  alternative of any yes–no question ([holmberg-2016], footnote to the section on positive and
  negative bias), is not modelled.
* The two versions of the negative particle in polarity-based languages, an interpretable one
  valuing the head and an uninterpretable one agreeing with a negation that values it, are one
  `AnswerFeature.value .negative`, whose agreement is built into `AnswerFeature.answer`.
* A negation inside the clause is the inner negation of [ladd-1981], negatively biased, and a
  high negation the outer one, positively biased ([holmberg-2016]). The classification is of
  readings, not of forms: the preposed *-n't* of *Isn't this the road to Lund?*, the high
  negation form of [romero-han-2004], has both readings for some speakers, so `ClauseNegation`
  is no refinement of `PolarQuestionForm`.

## References

* [holmberg-2016]
* [farkas-bruce-2010]
* [ladd-1981]
* [romero-han-2004]
-/

@[expose] public section

/-- The two systems for answering negative yes–no questions ([holmberg-2016]), told apart by the
particle that confirms the negative alternative of *Does John not drink coffee?*. -/
inductive AnsweringSystem where
  /-- The affirmative particle confirms the negative alternative (Japanese, Cantonese, Thai). -/
  | truthBased
  /-- The negative particle confirms the negative alternative (Swedish, Finnish, English with
  the middle reading of *not*). -/
  | polarityBased
  deriving DecidableEq, Repr

/-- The feature an answer particle spells out ([holmberg-2016]): a valued polarity feature, or
the affirmative polarity-reversing feature of *jo*, `[jo, +Pol, REV]`. -/
inductive AnswerFeature where
  /-- A valued polarity feature, [+Pol] or [−Pol]. -/
  | value (p : Polarity)
  /-- [+Pol, REV]: positive polarity eliminating a negation in the answer. -/
  | reversing
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

/-- The negation of a clause relative to its polarity head, if any. An answer inherits the
negation of the clause it answers. -/
inductive ClauseNegation where
  /-- No negation: a neutral question or a positive statement. -/
  | absent
  /-- A negation of the given height, nothing intervening between it and the polarity head. -/
  | height (h : NegationHeight)
  /-- A middle negation screened from the polarity head by an adverb scoping over it, as in
  Swedish *Har Johan nångång inte kommit i tid?*. -/
  | screened
  deriving DecidableEq, Repr

namespace ClauseNegation

variable (n : ClauseNegation)

/-- The negation is inside the clause the answer inherits, so that both alternatives of the
question contain it: a low or middle negation. -/
def InClause : Prop := n = .height .low ∨ n = .height .middle ∨ n = .screened

instance : Decidable n.InClause := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The polarity of the question's primary alternative relative to its positive alternative:
negative when the negation is inside the inherited clause. -/
def polarity : Polarity := if n.InClause then .negative else .positive

/-- The negation values the polarity head: a middle negation not screened off by an adverb. -/
def ValuesHead : Prop := n = .height .middle

instance : Decidable n.ValuesHead := inferInstanceAs (Decidable (_ = _))

variable {n}

theorem polarity_of_inClause (h : n.InClause) : n.polarity = .negative := by
  simp [polarity, h]

end ClauseNegation

/-- A polar interrogative: its sentence radical, the positive alternative, and its negation. -/
structure PolarInterrogative (W : Type*) where
  /-- The sentence radical, the positive alternative. -/
  radical : Set W
  /-- The negation of the interrogative. -/
  negation : ClauseNegation

namespace PolarInterrogative

open Semantics

variable {W : Type*} (q : PolarInterrogative W)

/-- The primary alternative: the radical under the polarity its negation gives it, negative when
the negation is inside the clause. -/
def primary : Set W := q.negation.polarity • q.radical

/-- A polar interrogative denotes the polar question of its primary alternative, the
disjunction of that alternative and its negation. -/
instance : Denotes (PolarInterrogative W) (Question W) := ⟨fun q ↦ Question.polar q.primary⟩

theorem denote_def : ⟦q⟧ = Question.polar q.primary := rfl

/-- A negative interrogative denotes the same question as its positive counterpart: the negation
decides which alternative is primary, not what the alternatives are. -/
@[simp] theorem denote_eq_polar_radical : ⟦q⟧ = Question.polar q.radical :=
  Question.polar_smul _ _

/-- A polar interrogative with a nontrivial radical offers exactly two alternatives, the two
values of its polarity variable. -/
theorem alt_denote {q : PolarInterrogative W} (hne : q.radical ≠ ∅)
    (hnu : q.radical ≠ Set.univ) : Question.alt ⟦q⟧ = {q.radical, q.radicalᶜ} := by
  rw [denote_eq_polar_radical]
  exact Question.alt_polar_of_nontrivial hne hnu

end PolarInterrogative

namespace AnswerFeature

open ClauseNegation

/-- The polarity of the alternative an answer confirms, relative to the positive alternative,
or `none` when the answer is ill formed. A reversing feature eliminates the negation inside the
inherited clause and values the head, and is ill formed without one. Otherwise, if the negation
values the head, a negative feature agrees with it and an affirmative one clashes with it; if
not, the feature values the head, composing with a negation inside the clause. -/
def answer : AnswerFeature → ClauseNegation → Option Polarity
  | reversing, n => if n.InClause then some .positive else none
  | value p, n =>
    if n.ValuesHead then (if p = .negative then some .negative else none)
    else some (p * n.polarity)

variable {n : ClauseNegation}

/-- A reversing feature eliminates the negation inside the clause and values the head. -/
theorem answer_reversing_of_inClause (h : n.InClause) : reversing.answer n = some .positive := by
  simp [answer, h]

/-- A reversing feature has no negation to eliminate outside a negative-bias question. -/
theorem answer_reversing_of_not_inClause (h : ¬ n.InClause) : reversing.answer n = none := by
  simp [answer, h]

/-- A negation valuing the head: a negative feature agrees with it, confirming the negative
alternative, and an affirmative one clashes with it. -/
theorem answer_value_of_valuesHead {p : Polarity} (h : n.ValuesHead) :
    (value p).answer n = if p = .negative then some .negative else none := by
  simp [answer, h]

/-- Without a negation valuing the head, a valued feature values it and composes with the
polarity of the primary alternative. -/
theorem answer_value_of_not_valuesHead {p : Polarity} (h : ¬ n.ValuesHead) :
    (value p).answer n = some (p * n.polarity) := by
  simp [answer, h]

/-- A negation inside the clause that does not value the head admits every feature, so a
truth-based configuration has no need of a reversing particle. -/
theorem answer_ne_none_of_inClause (f : AnswerFeature) (hi : n.InClause) (h : ¬ n.ValuesHead) :
    f.answer n ≠ none := by
  cases f
  · simp [answer_value_of_not_valuesHead h]
  · simp [answer_reversing_of_inClause hi]

/-- The answers a feature gives to polar questions whose negations are among `N`: the polarity
of a question's primary alternative, and that of the alternative the answer confirms. -/
def responses (f : AnswerFeature) (N : Set ClauseNegation) : Set Discourse.Response :=
  {x | x.reactsTo = .polarQuestion ∧
    ∃ n ∈ N, n.polarity = x.antecedent ∧ f.answer n = some x.polarity}

/-- REV is [reverse, +] ([farkas-bruce-2010]): once some negation of `N` is inside the clause,
a reversing feature gives exactly the positive answers reversing the primary alternative. -/
theorem responses_reversing {N : Set ClauseNegation} (hN : ∃ n ∈ N, n.InClause) :
    reversing.responses N = {x | x.reactsTo = .polarQuestion ∧ x.relative = .negative ∧
      x.polarity = .positive} := by
  obtain ⟨n₀, hn₀, hi₀⟩ := hN
  ext ⟨m, a, p⟩
  simp only [responses, Set.mem_ofPred_eq, Discourse.Response.relative_mk]
  constructor
  · rintro ⟨rfl, n, -, rfl, h⟩
    by_cases hi : n.InClause
    · rw [answer_reversing_of_inClause hi, Option.some_inj] at h
      subst h
      rw [polarity_of_inClause hi]
      exact ⟨rfl, rfl, rfl⟩
    · rw [answer_reversing_of_not_inClause hi] at h
      cases h
  · rintro ⟨rfl, ha, rfl⟩
    refine ⟨rfl, n₀, hn₀, ?_, answer_reversing_of_inClause hi₀⟩
    rw [polarity_of_inClause hi₀]
    cases a
    · exact absurd ha (by decide)
    · rfl

end AnswerFeature

/-- The answering system a negative-bias question exhibits at each height of its negation:
truth-based for the low negation, polarity-based otherwise. -/
def NegationHeight.predictedSystem : NegationHeight → AnsweringSystem
  | .low    => .truthBased
  | .middle => .polarityBased
  | .high   => .polarityBased

/-- The classification is read off the mechanism: a height is truth-based iff an affirmative
feature confirms the negative alternative of the question with that negation. -/
theorem NegationHeight.predictedSystem_eq_truthBased_iff (h : NegationHeight) :
    h.predictedSystem = .truthBased ↔
      (AnswerFeature.value .positive).answer (.height h) = some .negative := by
  cases h <;> decide
