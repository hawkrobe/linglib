module

public import Linglib.Semantics.Questions.Answering
public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Fragments.Swedish.Particles
public import Linglib.Data.Examples.Holmberg2016

/-!
# Holmberg (2016): The Syntax of Yes and No

This file formalizes [holmberg-2016]'s account of answers to yes–no questions. A question
contains an unvalued polarity head whose two values yield the Hamblin set of the question
(`questionSet`), and an answer is a full sentence: a focused valued polarity feature, spelled
out by a particle or an echoed verb, merged with the PolP inherited from the question and
eliding it, so that it chooses one of the two alternatives (`smul_mem_alt`). The two systems for
answering negative questions follow from the syntax of negation (`Question.PolP.answer`): a
middle negation values the polarity head before the particle can, so a plain affirmative clashes
and the negative particle confirms the negative alternative, while a low negation is out of
reach, so *yes* confirms the negative alternative and *no* is a double negation. English
speakers who read *not* low and those who read it middle both take a bare answer to *Is John
not coming?* to mean that he is not coming (`negative_neutralization`); an adverb preceding
*not* forces the low reading, and in Swedish, which has no low negation, an adverb screens the
middle negation from the polarity head to the same effect (`swedish_adverb`).

Section 4.4 defines the polarity-based system as the one lacking low negation
(`PolarityBased`, equivalently every negation height polarity-based, `polarityBased_iff`). Such a
language has no negative neutralization (`PolarityBased.answer_ne_negative`); Swedish, whose
negation is never low, is one (`swedish_polarityBased`), so confirming the positive alternative
of a negative question takes the polarity-reversing *jo* (`swedish_negative_question`), which a
truth-based configuration never needs (`no_reversal_needed_truth_based`). Positive-bias questions
carry a high negation outside the PolP and are answered like neutral questions
(`high_answers_like_neutral`). The mechanism predicts the judgment of every example answered by
a single particle of the study, whose question is neutral or whose negation the annotation
locates (`judgment_iff_predicted`).

## Implementation notes

* An answer is computed as a polarity relative to the question's positive alternative
  (`Question.PolP.answer`); the alternative it confirms is that polarity acting on the positive
  alternative. For *Har Johan nångång inte kommit i tid?* the positive alternative is that Johan
  has always been on time.
* Section 4.7 revises the height criterion: what matters is whether the negation can value the
  polarity head (`Question.PolP.ValuedByNegation`), which is how Thai questions come out
  truth-based. Thai and the Chinese question types (Section 4.9) are not formalized, nor are
  verb-echo answers and the structure of Finnish and Thai answers (Chapter 3), the two versions
  of *no* of Section 4.4, the higher-order alternative of positive-bias questions (Section 4.8),
  the table of languages with a reversing affirmative particle, and the global survey of
  Section 4.2.

## TODO

* The English, French and Japanese particles are defined here; they belong in fragments.

## References

* [holmberg-2016]
-/

@[expose] public section

namespace Holmberg2016

open Question

variable {W : Type*}

/-! ### The question variable -/

/-- The Hamblin set of the question with PolP `q` and positive alternative `p`: the primary
alternative and its negation. -/
def questionSet (q : PolP) (p : Set W) : Question W := polar (q.polarity • p)

/-- Every question with positive alternative `p`, negative or not, denotes the Hamblin set of
`p`; the questions differ in which alternative is primary (`PolP.polarity`). -/
theorem questionSet_eq (q : PolP) (p : Set W) : questionSet q p = polar p := polar_smul _ _

/-- A yes–no question with nontrivial positive alternative offers exactly two alternatives, the
two values of its polarity variable. -/
theorem alt_questionSet (q : PolP) {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    alt (questionSet q p) = {p, pᶜ} := by
  rw [questionSet_eq]
  exact alt_polar_of_nontrivial hne hnu

/-- An answer does not assert but chooses between the two alternatives of the question
(Section 5.1): whatever polarity it gives the positive alternative yields one of them. -/
theorem smul_mem_alt (q : PolP) {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
    (s : Polarity) : s • p ∈ alt (questionSet q p) := by
  rw [alt_questionSet q hne hnu]
  cases s <;> simp

/-- A neutral question. -/
def neutral : PolP := {}

/-- The negative question with a low negation. -/
def negLow : PolP := NegationHeight.low.toPolP

/-- The negative question with a middle negation. -/
def negMiddle : PolP := NegationHeight.middle.toPolP

/-- The positive-bias negative question, with a high negation. -/
def negHigh : PolP := NegationHeight.high.toPolP

/-- A middle negation screened from the polarity head by a preceding adverb, as in Swedish
*Har Johan nångång inte kommit i tid?*. -/
def screened : PolP := ⟨some .middle, true⟩

/-! ### English (Section 4.3) -/

/-- English *yes*. -/
def yes : AnswerParticle := { form := "yes", assigns := .positive }

/-- English *no*. -/
def no : AnswerParticle := { form := "no", assigns := .negative }

/-- Negative neutralization: speakers who read *not* low take *yes* to confirm that John is not
coming, speakers who read it middle take *no* to, so the two answers mean the same. -/
theorem negative_neutralization :
    negLow.answer yes = some .negative ∧ negMiddle.answer no = some .negative := by
  decide

/-- With the middle reading of *not*, bare *yes* is not a well-formed answer. -/
theorem yes_ill_formed_middle : negMiddle.answer yes = none := by decide

/-- With the low reading, *no* is grammatically a double negation confirming the positive
alternative; since bare *no* is parsed as the simpler plain negation, the continuation of *No,
he is* is compulsory. -/
theorem no_double_negation : negLow.answer no = some .positive := by decide

/-! ### The polarity-based system (Section 4.4) -/

/-- The polarity-based system, defined in Section 4.4 as the system which lacks low negation: a
language whose negations take the heights `N`. -/
def PolarityBased (N : Finset NegationHeight) : Prop := .low ∉ N

instance (N : Finset NegationHeight) : Decidable (PolarityBased N) :=
  inferInstanceAs (Decidable (_ ∉ _))

/-- A language is polarity-based iff each of its negation heights is. -/
theorem polarityBased_iff {N : Finset NegationHeight} :
    PolarityBased N ↔ ∀ n ∈ N, n.predictedSystem = .polarityBased := by
  refine ⟨fun hN n hn ↦ ?_, fun H hl ↦ absurd (H _ hl) (by decide)⟩
  cases n
  exacts [absurd hn hN, rfl, rfl]

/-- A polarity-based language has no negative neutralization: no plain affirmative particle
confirms the negative alternative of a negative question, unless an adverb screens the
negation. -/
theorem PolarityBased.answer_ne_negative {N : Finset NegationHeight} (hN : PolarityBased N)
    {n : NegationHeight} (hn : n ∈ N) {a : AnswerParticle} (ha : a.assigns = .positive)
    (hr : a.reverses = false) : n.toPolP.answer a ≠ some .negative := by
  rw [ne_eq, ← NegationHeight.predictedSystem_eq_truthBased_iff n ha hr,
    polarityBased_iff.1 hN n hn]
  decide

/-! ### Swedish (Section 4.5) and the reversing particles -/

open Swedish.Particles (ja nej jo)

/-- The heights of Swedish negation: middle, and high in positive-bias questions
(Section 4.8). Swedish has no low negation, hence no double negation
*Du kan inte inte gå i kyrkan* (Section 4.5). -/
def swedishNegation : Finset NegationHeight := {.middle, .high}

theorem swedish_polarityBased : PolarityBased swedishNegation := by decide

/-- *Ja* never confirms the negative alternative of a Swedish negative question. -/
theorem swedish_ja_ne_negative {n : NegationHeight} (hn : n ∈ swedishNegation) :
    n.toPolP.answer ja ≠ some .negative :=
  swedish_polarityBased.answer_ne_negative hn rfl rfl

/-- To *Har Johan inte kommit?* the plain affirmative *ja* is ill formed, *nej* confirms that he
has not come, and the reversing *jo* confirms that he has. -/
theorem swedish_negative_question :
    negMiddle.answer ja = none ∧ negMiddle.answer nej = some .negative ∧
      negMiddle.answer jo = some .positive := by
  decide

/-- *Har Johan nångång inte kommit i tid?*: the adverb intervening between the negation and the
polarity head lets *ja* confirm the negative alternative, although Swedish has no low
negation. -/
theorem swedish_adverb :
    screened.answer ja = some .negative ∧ screened.answer nej = some .positive := by
  decide

/-- French *si*: the reversing affirmative that *oui* cannot replace after a negative
question. -/
def si : AnswerParticle := { form := "si", assigns := .positive, reverses := true }

/-- French *oui*. -/
def oui : AnswerParticle := { form := "oui", assigns := .positive }

theorem french_negative_question :
    negMiddle.answer oui = none ∧ negMiddle.answer si = some .positive := by
  decide

/-- Reversing particles are needed only where a negation values the polarity head: in a
truth-based configuration every particle yields a well-formed answer, which is why no language
with a reversing affirmative particle clearly employs the truth-based system. -/
theorem no_reversal_needed_truth_based (a : AnswerParticle) : negLow.answer a ≠ none :=
  PolP.answer_ne_none_of_negationInside (by decide) (by decide)

/-! ### Japanese (Section 4.1) -/

/-- Japanese *un*. -/
def un : AnswerParticle := { form := "un", assigns := .positive }

/-- Japanese *uun*. -/
def uun : AnswerParticle := { form := "uun", assigns := .negative }

/-- On the prediction of Section 4.10 that the Japanese negation in a negative-bias question does
not value the polarity head, being low, *un* confirms that he does not drink coffee and *uun*
that he does. -/
theorem japanese_negative_question :
    negLow.answer un = some .negative ∧ negLow.answer uun = some .positive := by
  decide

/-! ### Positive-bias questions (Section 4.8) -/

/-- A positive-bias negative question, with the negation in the C-domain above the polarity
head, is answered like a neutral question. -/
theorem high_answers_like_neutral (a : AnswerParticle) : negHigh.answer a = neutral.answer a :=
  rfl

/-! ### The examples -/

open Data.Examples

/-- The answer particles of the examples. -/
def particles : List AnswerParticle := [yes, no, ja, nej, jo, oui, si, un, uun]

/-- The PolP of a negative question, by where the annotation locates its negation. -/
def negationTable : List (String × PolP) :=
  [("low", negLow), ("middle", negMiddle), ("middle behind an adverb", screened),
    ("high", negHigh)]

/-- The alternatives an example confirms, as polarities relative to the positive alternative. -/
def polarityTable : List (String × Polarity) := [("p", .positive), ("not p", .negative)]

/-- An example of a single particle answering a question whose PolP the example fixes. -/
structure Row where
  /-- The PolP of the question. -/
  polP : PolP
  /-- The answer. -/
  particle : AnswerParticle
  /-- The alternative the answer confirms or is intended to confirm, if the example says. -/
  target : Option Polarity
  /-- The judgment of the answer. -/
  judgment : Judgment
  deriving DecidableEq, Repr

/-- The row of an example: its question is neutral or its negation located, and its answer is a
single particle of `particles`. -/
def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let polP ← if ex.feature? "question" = some "neutral" then some neutral
    else ex.parse? "negation" negationTable
  let particle ← particles.find? (ex.feature? "answer" == some ·.form)
  let target := ex.parse? "confirms" polarityTable <|> ex.parse? "intended" polarityTable
  pure ⟨polP, particle, target, ex.judgment⟩

/-- The rows of the examples. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The answer is well formed and confirms the alternative the example targets, if any. -/
def Row.Predicted (r : Row) : Prop :=
  r.polP.answer r.particle ≠ none ∧ (r.target = none ∨ r.polP.answer r.particle = r.target)

instance : DecidablePred Row.Predicted := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The rows include *Har Johan inte kommit?* answered by *\*Ja* and by *Jo* (Section 4.5). -/
theorem kommit_mem_rows :
    ⟨negMiddle, ja, none, .unacceptable⟩ ∈ rows ∧
      ⟨negMiddle, jo, some .positive, .acceptable⟩ ∈ rows := by
  decide

/-- The mechanism predicts the judgment of every example answered by a single particle of the
study, whose question is neutral or whose negation the annotation locates: the example is
acceptable just when the answer is well formed and confirms the alternative it targets. -/
theorem judgment_iff_predicted : ∀ r ∈ rows, (r.judgment = .acceptable ↔ r.Predicted) := by
  decide

end Holmberg2016
