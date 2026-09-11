import Linglib.Features.Polarity
import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Tactic.TypeStar

/-!
# Answering System Typology
[holmberg-2016]

Cross-linguistic variation in how languages answer polar questions.

## The Binary Parameter

[holmberg-2016]'s central typological contribution: languages divide into
two types based on what "yes" means in response to a negative question
("Doesn't John drink?"):

- **Truth-based**: "yes" affirms the proposition in the question.
  To "Doesn't he drink?", "yes" = "he doesn't drink" (Japanese, Mandarin, Thai).
- **Polarity-based**: "yes" assigns positive polarity.
  To "Doesn't he drink?", "yes" = "he does drink" (English, Swedish, German).

## Answer Strategy

Orthogonally, languages vary in whether answers use dedicated particles
or echo the finite verb:

- **Particle**: dedicated yes/no words (English *yes/no*, Japanese *hai/iie*)
- **Verb echo**: echoed finite verb (Finnish *juo/ei juo*, Welsh *ydy/nac ydy*)
- **Mixed**: both available (Swedish *ja/nej* + verb echo)

## Connection to PolP

In [holmberg-2016]'s syntax, every finite clause has a polarity head
(PolP) bearing a valued or unvalued [±Pol] feature. In polar questions,
[±Pol] is unvalued — the answer values it. The answering system parameter
determines whether "yes" values the variable as [+Pol] (polarity-based)
or affirms the question's primary proposition (truth-based).
-/

namespace Features

/-- How a language interprets "yes" in response to negative polar questions.

    The diagnostic: "Doesn't John drink?" → "Yes" means...
    - Truth-based: "He doesn't drink" (affirms the proposition)
    - Polarity-based: "He does drink" (assigns positive polarity) -/
inductive AnsweringSystem where
  /-- "Yes" affirms the proposition in the question (Japanese, Mandarin, Thai, Cantonese) -/
  | truthBased
  /-- "Yes" assigns positive polarity (English, Swedish, German, French, Finnish) -/
  | polarityBased
  deriving DecidableEq, Repr

/-- How a language forms answers to polar questions.

    Orthogonal to `AnsweringSystem` — either system can combine with
    either strategy. -/
inductive AnswerStrategy where
  /-- Dedicated yes/no particles (English *yes/no*, Japanese *hai/iie*) -/
  | particle
  /-- Echoed finite verb (Finnish *juo/ei juo*, Welsh *ydy/nac ydy*) -/
  | verbEcho
  /-- Both particle and verb echo available (Swedish *ja/nej* + verb echo) -/
  | mixed
  deriving DecidableEq, Repr

/-- A language's polar answer profile: answering system + answer strategy. -/
structure PolarAnswerProfile where
  /-- How "yes" is interpreted relative to negative questions -/
  system : AnsweringSystem
  /-- How answers are formed (particle, verb echo, or both) -/
  strategy : AnswerStrategy
  /-- Does the language have a dedicated polarity-reversing particle
      (e.g., Swedish *jo*, German *doch*, French *si*)? -/
  hasPolarityReversal : Bool := false
  deriving DecidableEq, Repr

/-- The diagnostic prediction: what does "yes" mean in response to
    "Doesn't John drink?" under each answering system?

    Returns the polarity of the proposition expressed by "yes". -/
def AnsweringSystem.yesToNegativeQuestion : AnsweringSystem → Features.Polarity
  | .truthBased    => .negative  -- "yes" = "he doesn't drink"
  | .polarityBased => .positive  -- "yes" = "he does drink"

/-- Truth-based and polarity-based systems give opposite answers
    to negative questions. -/
theorem answering_systems_diverge_on_negative :
    AnsweringSystem.truthBased.yesToNegativeQuestion ≠
    AnsweringSystem.polarityBased.yesToNegativeQuestion := by decide

/-! ## The valuation of the polarity head

[holmberg-2016]'s explanation of the two systems (Chapter 4): every finite clause has a
polarity head, merged unvalued and moved to the C-domain in a question, so that the question
denotes the set of its two valuations. An answer merges a focused valued polarity feature,
spelled out by a particle or an echoed verb, with the PolP inherited from the question, and
values the head unless a negation inside that PolP is close enough to value it first. A
*middle* negation, in a local c-command relation to the head, values it negative, so an
affirmative particle clashes with it and only a negative particle, agreeing with the negation,
or a polarity-reversing particle, which eliminates it, is well formed: the polarity-based
system. A *low*, VP-internal negation, or a middle one screened off by an adverb scoping over
it, is out of reach, so the particle values the head itself and the affirmative answer confirms
the negative alternative: the truth-based system. A *high* negation sits outside the PolP,
and the question is answered like a neutral one. -/

/-- An answer particle: assigns a polarity, responds to antecedent
contexts of the recorded polarities. Answer particles are pro-sentential, deliberately
outside the host-associated `Syntax/Category/Particle` core; reversal-hood is derived, not
stored. -/
structure AnswerParticle where
  /-- Citation form. -/
  form : String
  /-- The polarity value assigned to [±Pol]. -/
  assigns : Polarity
  /-- Polarities of antecedent context the particle can respond to. -/
  respondsTo : List Polarity
  deriving DecidableEq, Repr

/-- A polarity-reversing particle assigns [+Pol] while responding only
to negative contexts (Swedish *jo*, German *doch*, French *si*;
[holmberg-2016]). -/
def AnswerParticle.IsReversal (p : AnswerParticle) : Prop :=
  p.assigns = .positive ∧ p.respondsTo = [.negative]

instance : DecidablePred AnswerParticle.IsReversal :=
  λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Structural height of a sentential negation relative to the polarity head. The height
classifies constructions, not languages: English has middle negation by default, low negation
under a scoping adverb, and high negation in positive-bias questions. -/
inductive NegationHeight where
  /-- Negation below the reach of the polarity head, VP-internal (Japanese, Mandarin, Thai). -/
  | low
  /-- Negation in a local c-command relation to the polarity head (English by default, Swedish,
  Finnish, German). -/
  | middle
  /-- Negation above the polarity head, in the C-domain (English *-n't* in positive-bias
  questions). -/
  | high
  deriving DecidableEq, Repr

/-- The PolP an answer inherits from a yes–no question: the proposition below the negation,
the negation's height (`none` for a neutral question), and whether an adverb scoping over a
middle negation keeps it from valuing the polarity head. -/
structure PolP (W : Type*) where
  /-- The proposition below the negation. -/
  prejacent : Set W
  /-- The height of the negation, if any. -/
  negation : Option NegationHeight := none
  /-- An adverb scoping over a middle negation, as in Swedish *nångång inte*. -/
  intervener : Bool := false

namespace PolP

variable {W : Type*} (q : PolP W)

/-- The negation sits inside the PolP, so that both alternatives of the question contain it. -/
def NegationInside : Prop := q.negation = some .low ∨ q.negation = some .middle

instance : Decidable q.NegationInside := inferInstanceAs (Decidable (_ ∨ _))

/-- The proposition the PolP expresses under positive polarity, the primary alternative of the
question: the negated prejacent when the negation is inside the PolP. -/
def content : Set W := if q.NegationInside then q.prejacentᶜ else q.prejacent

/-- The negation values the polarity head: a middle negation not screened off by an adverb. -/
def ValuedByNegation : Prop := q.negation = some .middle ∧ q.intervener = false

instance : Decidable q.ValuedByNegation := inferInstanceAs (Decidable (_ ∧ _))

/-- The proposition an answer particle expresses, or `none` when the answer is ill formed: if
the negation values the head, a negative particle agrees with it and confirms the negative
alternative, a reversing particle eliminates it, and any other affirmative particle clashes;
otherwise the particle values the head and the answer is the primary alternative or its
negation. -/
def answer (a : AnswerParticle) : Option (Set W) :=
  if q.ValuedByNegation then
    if a.assigns = .negative then some q.content
    else if a.IsReversal then some q.prejacent else none
  else if a.assigns = .positive then some q.content else some q.contentᶜ

variable {q} {a : AnswerParticle}

theorem content_of_low (hq : q.negation = some .low) : q.content = q.prejacentᶜ := by
  simp [content, NegationInside, hq]

theorem content_of_middle (hq : q.negation = some .middle) : q.content = q.prejacentᶜ := by
  simp [content, NegationInside, hq]

theorem content_of_high (hq : q.negation = some .high) : q.content = q.prejacent := by
  simp [content, NegationInside, hq]

theorem content_of_neutral (hq : q.negation = none) : q.content = q.prejacent := by
  simp [content, NegationInside, hq]

/-- Without a negation valuing the head, the particle values it: the affirmative particle
expresses the primary alternative and the negative one its negation. -/
theorem answer_of_not_valued (h : ¬ q.ValuedByNegation) :
    q.answer a = if a.assigns = .positive then some q.content else some q.contentᶜ := by
  simp [answer, h]

/-- Without a negation valuing the head, every particle yields a well-formed answer, so a
truth-based configuration has no need of a reversing particle. -/
theorem answer_ne_none_of_not_valued (h : ¬ q.ValuedByNegation) : q.answer a ≠ none := by
  rw [answer_of_not_valued h]; split <;> simp

/-- Low negation, affirmative particle: the negative alternative is confirmed. -/
theorem answer_low_positive (hq : q.negation = some .low) (ha : a.assigns = .positive) :
    q.answer a = some q.prejacentᶜ := by
  simp [answer, ValuedByNegation, content, NegationInside, hq, ha]

/-- Low negation, negative particle: double negation confirms the positive alternative. -/
theorem answer_low_negative (hq : q.negation = some .low) (ha : a.assigns = .negative) :
    q.answer a = some q.prejacent := by
  simp [answer, ValuedByNegation, content, NegationInside, hq, ha, compl_compl]

/-- Middle negation, plain affirmative particle: a feature clash, no well-formed answer. -/
theorem answer_middle_positive (hq : q.negation = some .middle) (hi : q.intervener = false)
    (ha : a.assigns = .positive) (hr : ¬ a.IsReversal) : q.answer a = none := by
  simp [answer, ValuedByNegation, hq, hi, ha, hr]

/-- Middle negation, reversing particle: the negation is eliminated and the positive
alternative confirmed. -/
theorem answer_middle_reversal (hq : q.negation = some .middle) (hi : q.intervener = false)
    (hr : a.IsReversal) : q.answer a = some q.prejacent := by
  simp [answer, ValuedByNegation, hq, hi, hr, hr.1]

/-- Middle negation, negative particle: negative concord confirms the negative alternative. -/
theorem answer_middle_negative (hq : q.negation = some .middle) (hi : q.intervener = false)
    (ha : a.assigns = .negative) : q.answer a = some q.prejacentᶜ := by
  simp [answer, ValuedByNegation, content, NegationInside, hq, hi, ha]

/-- A middle negation behind an intervening adverb behaves like a low one. -/
theorem answer_intervened (hq : q.negation = some .middle) (hi : q.intervener = true) :
    q.answer a = if a.assigns = .positive then some q.prejacentᶜ else some q.prejacent := by
  simp [answer, ValuedByNegation, content, NegationInside, hq, hi, compl_compl]

/-- A neutral question: the affirmative particle confirms the prejacent, the negative one its
negation. -/
theorem answer_neutral (hq : q.negation = none) :
    q.answer a = if a.assigns = .positive then some q.prejacent else some q.prejacentᶜ := by
  simp [answer, ValuedByNegation, content, NegationInside, hq]

/-- A high negation sits outside the PolP, so the question is answered like a neutral one. -/
theorem answer_high (hq : q.negation = some .high) :
    q.answer a = if a.assigns = .positive then some q.prejacent else some q.prejacentᶜ := by
  simp [answer, ValuedByNegation, content, NegationInside, hq]

end PolP

/-- The answering system a negative-bias question exhibits at each height of its negation:
truth-based for the low negation, polarity-based otherwise. -/
def NegationHeight.predictedSystem : NegationHeight → AnsweringSystem
  | .low    => .truthBased
  | .middle => .polarityBased
  | .high   => .polarityBased

/-- The classification is read off the mechanism: a height is truth-based iff a plain
affirmative particle confirms the negative alternative of every question with that negation. -/
theorem NegationHeight.predictedSystem_eq_truthBased_iff {W : Type*} [Nonempty W]
    (h : NegationHeight) {a : AnswerParticle} (ha : a.assigns = .positive)
    (hr : ¬ a.IsReversal) :
    h.predictedSystem = .truthBased ↔
      ∀ p : Set W, (⟨p, some h, false⟩ : PolP W).answer a = some pᶜ := by
  cases h
  · simp only [predictedSystem, true_iff]
    exact λ p => PolP.answer_low_positive rfl ha
  · simp only [predictedSystem, reduceCtorEq, false_iff, not_forall]
    exact ⟨∅, by rw [PolP.answer_middle_positive rfl rfl ha hr]; simp⟩
  · simp only [predictedSystem, reduceCtorEq, false_iff, not_forall]
    refine ⟨∅, ?_⟩
    rw [PolP.answer_high rfl]
    simp [ha, Set.compl_empty, Set.empty_ne_univ]

end Features
