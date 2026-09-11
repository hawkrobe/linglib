import Linglib.Features.AnsweringSystem
import Linglib.Semantics.Questions.Hamblin
import Linglib.Fragments.Swedish.AnswerParticles
import Linglib.Fragments.German.PolarityMarking

/-!
# Holmberg (2016): The Syntax of Yes and No

This file formalizes [holmberg-2016]'s account of answers to yes–no questions. A question
contains an unvalued polarity head whose two values yield the Hamblin set of the question
(`questionSet`), and an answer is a full sentence: a focused valued polarity feature, spelled
out by a particle or an echoed verb, merged with the PolP inherited from the question and
eliding it. The two systems for answering negative questions follow from the syntax of
negation: a middle negation values the polarity head before the particle can, so a plain
affirmative clashes and the negative particle confirms the negative alternative (the
polarity-based system of Swedish, Finnish and English with the middle reading of *not*), while a
low negation is out of reach, so *yes* confirms the negative alternative and *no* denies it
(the truth-based system of Japanese, Cantonese, Thai and English with the low reading). English
speakers who read *not* low and those who read it middle both take a bare answer to *Is John
not coming?* to mean that he is not coming (`negative_neutralization`), an adverb scoping over
the negation forces the low reading (`adverb_forces_truth_based`) even in Swedish, which has no
low negation, and confirming the positive alternative of a negative question needs a
polarity-reversing particle such as Swedish *jo* or French *si* (`jo_reverses`) or the double
negation of *No, he is*. Positive-bias questions carry a high negation outside the PolP and are
answered like neutral questions (`high_answers_like_neutral`).

## Implementation notes

* The valuation mechanism is the substrate `Features.PolP.answer`; the study instantiates it
  with the particles of the fragments and the negation heights the book assigns to each
  construction. The book's Table 4.2 of reversing particles and the global survey of Section
  4.2 are not encoded.
* Verb-echo answers, the structure of Finnish and Thai answers (Chapter 3) and the Chinese
  question types (Section 4.9) are not formalized.

## References

* [holmberg-2016]
-/

namespace Holmberg2016

open Features Question

variable {W : Type*}

/-! ### The question variable -/

/-- The Hamblin set of the question: the primary alternative and its negation. -/
def questionSet (q : PolP W) : Question W := polar q.content

/-- A yes–no question with nontrivial content offers exactly two alternatives, the two values
of its polarity variable. -/
theorem alt_question (q : PolP W) (hne : q.content ≠ ∅) (hnu : q.content ≠ Set.univ) :
    alt (questionSet q) = {q.content, q.contentᶜ} :=
  alt_polar_of_nontrivial hne hnu

/-- A neutral question. -/
def neutral (p : Set W) : PolP W := ⟨p, none, false⟩

/-- A negative-bias question whose negation has the given height. -/
def negative (h : NegationHeight) (p : Set W) : PolP W := ⟨p, some h, false⟩

/-- The negative question with a low negation. -/
abbrev negLow (p : Set W) : PolP W := negative .low p

/-- The negative question with a middle negation. -/
abbrev negMiddle (p : Set W) : PolP W := negative .middle p

/-- A negative question denotes the same Hamblin set as its neutral counterpart, as Hamblin
noted; the two differ in which alternative is primary (`PolP.content`). -/
theorem negative_question_eq_neutral (h : NegationHeight) (p : Set W) :
    questionSet (negative h p) = questionSet (neutral p) := by
  unfold questionSet
  cases h <;> simp [PolP.content, PolP.NegationInside, negative, neutral]

/-! ### English (Section 4.3) -/

/-- English *yes*: assigns positive polarity in any context. -/
def yes : AnswerParticle := ⟨"yes", .positive, [.positive, .negative]⟩

/-- English *no*: assigns negative polarity in any context. -/
def no : AnswerParticle := ⟨"no", .negative, [.positive, .negative]⟩

/-- Negative neutralization: speakers who read *not* low take *yes* to confirm that John is not
coming, speakers who read it middle take *no* to, so the two answers mean the same. -/
theorem negative_neutralization (p : Set W) :
    (negLow p).answer yes = some pᶜ ∧ (negMiddle p).answer no = some pᶜ :=
  ⟨PolP.answer_low_positive rfl rfl, PolP.answer_middle_negative rfl rfl rfl⟩

/-- With the middle reading of *not*, bare *yes* is not a well-formed answer. -/
theorem yes_ill_formed_middle (p : Set W) : (negMiddle p).answer yes = none :=
  PolP.answer_middle_positive rfl rfl rfl (by decide)

/-- With the low reading, *no* is a double negation confirming the positive alternative, the
first clause of *No, he is*. -/
theorem no_double_negation (p : Set W) : (negLow p).answer no = some p :=
  PolP.answer_low_negative rfl rfl

/-- *Does John sometimes not show up on time?*: an adverb scoping over the negation keeps it from
valuing the polarity head, so every speaker answers truth-based. -/
theorem adverb_forces_truth_based (p : Set W) :
    (⟨p, some .middle, true⟩ : PolP W).answer yes = some pᶜ ∧
      (⟨p, some .middle, true⟩ : PolP W).answer no = some p := by
  simp [PolP.answer_intervened, yes, no]

/-! ### Swedish (Section 4.5) and the reversing particles -/

open Swedish.AnswerParticles in
/-- Swedish has only a middle negation: to *Har Johan inte kommit?* the plain affirmative *ja* is
ill formed, *nej* confirms that he has not come, and the reversing *jo* confirms that he has. -/
theorem swedish_negative_question (p : Set W) :
    (negMiddle p).answer ja = none ∧ (negMiddle p).answer nej = some pᶜ ∧
      (negMiddle p).answer jo = some p :=
  ⟨PolP.answer_middle_positive rfl rfl rfl ja_not_reversal,
    PolP.answer_middle_negative rfl rfl rfl, PolP.answer_middle_reversal rfl rfl jo_is_reversal⟩

open Swedish.AnswerParticles in
/-- *Har Johan nångång inte kommit i tid?*: the adverb intervening between the negation and the
polarity head lets *ja* confirm the negative alternative, although Swedish has no low
negation. -/
theorem swedish_adverb (p : Set W) :
    (⟨p, some .middle, true⟩ : PolP W).answer ja = some pᶜ ∧
      (⟨p, some .middle, true⟩ : PolP W).answer nej = some p := by
  simp [PolP.answer_intervened, ja, nej]

/-- The reversing particles of Swedish and German, read off the fragments. -/
theorem jo_reverses :
    Swedish.AnswerParticles.jo.IsReversal ∧ German.PolarityMarking.dochAnswer.IsReversal := by
  decide

/-- French *si*: the reversing affirmative that *oui* cannot replace after a negative question. -/
def si : AnswerParticle := ⟨"si", .positive, [.negative]⟩

/-- French *oui*. -/
def oui : AnswerParticle := ⟨"oui", .positive, [.positive]⟩

theorem french_negative_question (p : Set W) :
    (negMiddle p).answer oui = none ∧ (negMiddle p).answer si = some p :=
  ⟨PolP.answer_middle_positive rfl rfl rfl (by decide),
    PolP.answer_middle_reversal rfl rfl (by decide)⟩

/-- Reversing particles are only needed where a negation values the polarity head: in a
truth-based configuration every particle yields a well-formed answer, which is why the
languages of Table 4.2 are polarity-based. -/
theorem no_reversal_needed_truth_based (p : Set W) (a : AnswerParticle) :
    (negLow p).answer a ≠ none :=
  PolP.answer_ne_none_of_not_valued (by simp [PolP.ValuedByNegation, negLow, negative])

/-! ### Japanese and Cantonese (Sections 1.3 and 4.1) -/

/-- Japanese *un*. -/
def un : AnswerParticle := ⟨"un", .positive, [.positive, .negative]⟩

/-- Japanese *uun*. -/
def uun : AnswerParticle := ⟨"uun", .negative, [.positive, .negative]⟩

/-- With Japanese's low negation, *un* confirms that he does not drink coffee and *uun* that he
does. -/
theorem japanese_negative_question (p : Set W) :
    (negLow p).answer un = some pᶜ ∧ (negLow p).answer uun = some p :=
  ⟨PolP.answer_low_positive rfl rfl, PolP.answer_low_negative rfl rfl⟩

/-! ### Positive-bias questions (Section 4.8) -/

/-- A positive-bias negative question, with the negation in the C-domain above the polarity
head, is answered like a neutral question. -/
theorem high_answers_like_neutral (p : Set W) (a : AnswerParticle) :
    (negative .high p).answer a = (neutral p).answer a := by
  rw [PolP.answer_high rfl, PolP.answer_neutral rfl]; rfl

/-- A positive-bias question differs from the negative-bias one in its primary alternative,
which is the prejacent rather than its negation. -/
theorem content_high_ne_content_middle [Nonempty W] (p : Set W) :
    (negative .high p).content ≠ (negMiddle p).content := by
  rw [PolP.content_of_high rfl, PolP.content_of_middle rfl]
  show p ≠ pᶜ
  intro h
  obtain ⟨w⟩ := ‹Nonempty W›
  by_cases hw : w ∈ p
  · exact (h ▸ hw : w ∈ pᶜ) hw
  · exact hw (h ▸ hw : w ∈ p)

end Holmberg2016
