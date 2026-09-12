import Linglib.Data.Examples.KehlerRohde2013
import Linglib.Data.UD.Basic
import Linglib.Discourse.Coherence
import Linglib.Discourse.Centering.Pronominalization
import Linglib.Discourse.Centering.Instances.GrammaticalRole
import Linglib.Fragments.English.Pronouns
import Linglib.Syntax.Category.Pronoun.Capabilities
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Kehler and Rohde (2013): A Probabilistic Reconciliation of Coherence-Driven and Centering-Driven Theories of Pronoun Interpretation

This file formalizes the Bayesian model of pronoun interpretation of [kehler-rohde-2013]: the
interpreter's bias `P(referent | pronoun)` is proportional to the speaker's production bias
`P(pronoun | referent)` times the next-mention prior `P(referent)` (the paper's (11) and (13)),
the prior is the mixture of the relation-conditioned biases weighted by the expected coherence
relations ((9)), and coherence expectations are in turn the mixture over the referent mentioned
next ((12)). The consequences the paper draws are proved once: a shift in the expected relations
with the conditional biases held fixed shifts the prior (`mixture_sub`), and only then
(`mixture_const`); a referent pronominalized above the overall rate is the pronoun's referent
above its prior, the overlaid subject bias (`posterior_gt_iff`); and raising a referent's
next-mention probability raises the expectation of the relations that favor it
(`relationExpectation_sub`).

The paper's passage-completion results (Tables 1–10, `Data/Examples/KehlerRohde2013.json`) then
instantiate the model. The instruction manipulation's mixtures computed from Tables 3 and 4 fall
on the sides of chance Table 5 observes (`instruction_mixtures`); the pronoun prompt raises
subject mentions and shifts the continuations toward the Source-biased relations (Table 6); the
voice manipulation's Bayesian predictions computed from Tables 7 and 9 favor the subject in both
voices, more in the active, as Table 10 observes (`voice_predictions`); and the pronominalization
rates of Table 9 increase with topichood, the passive subject above the active subject above the
non-subjects, a gradient the backward-looking center of a grammatical-role Centering cannot see
(`cb_topichood_dissociation_under_voice`).

## Implementation notes

Rates are the paper's percentages, read from the rows with `nat?` and cast to `ℚ`; computed
quantities are compared through their integer numerators. Violated Expectation is
`CoherenceRelation.violatedExpectation`; relations the paper's coding does not record carry no
probability.

## References

* [kehler-rohde-2013]
* [hobbs-1979]
* [grosz-joshi-weinstein-1995]
* [davison-1984]
-/

namespace KehlerRohde2013

open Discourse.Coherence Discourse.Centering Finset
open Data.Examples (LinguisticExample)
open Morphology (Word)
open UD (Voice)

/-! ### The Bayesian model -/

section Model

variable {C R : Type*}

/-- (9): the next-mention probability of a referent as the mixture of its relation-conditioned
probabilities, weighted by the probabilities of the relations. -/
def mixture [Fintype C] (pCR bias : C → ℚ) : ℚ := ∑ c, pCR c * bias c

/-- The mixture is affine in the expected relations: a change of expectations with the
conditional biases fixed changes the next-mention probability by the change weighted by the
biases. -/
theorem mixture_sub [Fintype C] (p q bias : C → ℚ) :
    mixture q bias - mixture p bias = ∑ c, (q c - p c) * bias c := by
  simp only [mixture, ← sum_sub_distrib, sub_mul]

/-- Without relation-conditioning the mixture over a distribution is the common bias, whatever
the expectations: a heuristic account predicts no effect of the instructions. -/
theorem mixture_const [Fintype C] (p : C → ℚ) (hp : ∑ c, p c = 1) (b : ℚ) :
    mixture p (λ _ => b) = b := by
  simp only [mixture, ← sum_mul, hp, one_mul]

/-- (12): the probability of a coherence relation as the mixture over the referent mentioned
next. -/
def relationExpectation [Fintype R] (pRef : R → ℚ) (crGiven : R → C → ℚ) (c : C) : ℚ :=
  ∑ r, pRef r * crGiven r c

/-- A shift in next-mention expectations shifts the expected relations by the shift weighted by
each referent's relation profile. -/
theorem relationExpectation_sub [Fintype R] (p q : R → ℚ) (crGiven : R → C → ℚ) (c : C) :
    relationExpectation q crGiven c - relationExpectation p crGiven c =
      ∑ r, (q r - p r) * crGiven r c := by
  simp only [relationExpectation, ← sum_sub_distrib, sub_mul]

/-- (11), (13): the interpreter's posterior over referents, the production bias times the
next-mention prior, normalized by the overall probability of a pronoun. -/
def posterior [Fintype R] (pRef pPron : R → ℚ) (r : R) : ℚ :=
  pPron r * pRef r / ∑ r', pPron r' * pRef r'

/-- The overlaid bias: a referent is the pronoun's referent above its prior probability exactly
when it is pronominalized above the overall rate of pronominalization. -/
theorem posterior_gt_iff [Fintype R] (pRef pPron : R → ℚ) (r : R) (hr : 0 < pRef r)
    (hZ : 0 < ∑ r', pPron r' * pRef r') :
    pRef r < posterior pRef pPron r ↔ ∑ r', pPron r' * pRef r' < pPron r := by
  rw [posterior, lt_div_iff₀ hZ, mul_comm (pPron r), mul_lt_mul_iff_right₀ hr]

end Model

/-! ### The data

Each row of `Data/Examples/KehlerRohde2013.json` is a cell group of one of the paper's tables,
located by the table and its conditions. -/

/-- The first percentage the rows matching the features record under `key`. -/
def pct (fs : List (String × String)) (key : String) : ℕ :=
  ((Examples.all.filter λ e => fs.all λ kv => e.feature? kv.1 = some kv.2).filterMap
    (·.nat? key)).headD 0

/-- The paper's names for the coded relations. -/
def relationTag : CoherenceRelation → String
  | .occasion => "occasion"
  | .elaboration => "elaboration"
  | .explanation => "explanation"
  | .violatedExpectation => "violatedExpectation"
  | .result => "result"
  | .parallel => "parallel"
  | .contrast => "contrast"
  | .correction => "correction"
  | .background => "background"
  | .consequence => "consequence"
  | .alternation => "alternation"

/-- The instruction of the instruction manipulation. -/
inductive Instruction where
  | whatNext
  | why
  deriving DecidableEq, Repr

def Instruction.tag : Instruction → String
  | .whatNext => "whatNext"
  | .why => "why"

/-- Whether the prompt supplies a pronoun. -/
inductive Prompt where
  | pronoun
  | noPronoun
  deriving DecidableEq, Repr

def Prompt.tag : Prompt → String
  | .pronoun => "pronoun"
  | .noPronoun => "noPronoun"

/-- A referent by its grammatical position in the context sentence: the subject (the Source of a
Source–Goal transfer, the causally implicated referent of an active subject-biased verb) or the
non-subject. -/
inductive Position where
  | subject
  | nonSubject
  deriving DecidableEq, Repr, Fintype

/-- A function on positions by its two values. -/
def Position.select {α : Type*} (s n : α) : Position → α
  | .subject => s
  | .nonSubject => n

private theorem sum_position (f : Position → ℚ) : ∑ p, f p = f .subject + f .nonSubject := by
  rw [show (univ : Finset Position) = {.subject, .nonSubject} from by decide,
    sum_pair (by decide)]

def voiceTag : Voice → String
  | .Act => "active"
  | .Pass => "passive"
  | _ => ""

/-! ### Coherence-conditioned biases (Tables 1–5) -/

/-- Table 1: the Source interpretation rate by aspect. -/
def aspectSource (aspect : String) : ℕ :=
  pct [("table", "1"), ("aspect", aspect)] "sourceInterpretation"

/-- The event-structure hypothesis: the imperfective keeps the Source central, the perfective
focuses the end state, so the imperfective draws more Source interpretations. -/
theorem imperfective_more_source : aspectSource "perfective" < aspectSource "imperfective" := by
  decide

/-- Table 2: the frequency of a relation in the perfective continuations. -/
def perfectiveFrequency (c : CoherenceRelation) : ℕ :=
  pct [("table", "2"), ("relation", relationTag c)] "frequency"

/-- Table 2: the Source bias of a relation in the perfective continuations. -/
def perfectiveSourceGiven (c : CoherenceRelation) : ℕ :=
  pct [("table", "2"), ("relation", relationTag c)] "sourceGivenRelation"

private theorem mixture_div (p b : CoherenceRelation → ℕ) :
    mixture (λ c => (p c : ℚ) / 100) (λ c => (b c : ℚ) / 100) =
      ((∑ c, p c * b c : ℕ) : ℚ) / 10000 := by
  rw [eq_div_iff (by norm_num), mixture, sum_mul]
  push_cast
  refine sum_congr rfl λ c _ => ?_
  ring

/-- The near-chance overall bias of the perfective continuations is the mixture (9) of strongly
opposed relation-conditioned biases: Occasion, the most common relation, favors the Goal and
Elaboration the Source. -/
theorem perfective_mixture_masks_biases :
    2 / 5 < mixture (λ c => (perfectiveFrequency c : ℚ) / 100)
        (λ c => (perfectiveSourceGiven c : ℚ) / 100) ∧
      mixture (λ c => (perfectiveFrequency c : ℚ) / 100)
        (λ c => (perfectiveSourceGiven c : ℚ) / 100) < 3 / 5 ∧
      perfectiveSourceGiven .occasion < 20 ∧ 90 < perfectiveSourceGiven .elaboration ∧
      ∀ c, perfectiveFrequency c ≤ perfectiveFrequency .occasion := by
  have h : ∑ c, perfectiveFrequency c * perfectiveSourceGiven c = 5524 := by decide
  refine ⟨?_, ?_, by decide, by decide, by decide⟩ <;> rw [mixture_div, h] <;> norm_num

/-- Table 3: the frequency of a relation under an instruction. -/
def frequency (i : Instruction) (c : CoherenceRelation) : ℕ :=
  pct [("table", "3"), ("instruction", i.tag), ("relation", relationTag c)] "frequency"

/-- Table 4: the Source bias of a relation in the instruction experiment. -/
def sourceGiven (c : CoherenceRelation) : ℕ :=
  pct [("table", "4"), ("relation", relationTag c)] "instructionManipulation"

/-- Table 5: the observed Source interpretation rate under an instruction. -/
def observedSource (i : Instruction) : ℕ :=
  pct [("table", "5"), ("instruction", i.tag)] "sourceInterpretation"

/-- (9) on Tables 3 and 4: the next-mention probability of the Source under an instruction. -/
def predictedSource (i : Instruction) : ℚ :=
  mixture (λ c => (frequency i c : ℚ) / 100) (λ c => (sourceGiven c : ℚ) / 100)

/-- The instruction manipulation: the expectations of Table 3, with the conditional biases of
Table 4 held fixed, put the *Why?* mixture on the Source side of chance and the *What happened
next?* mixture on the Goal side, where Table 5 finds the interpretations of identical stimuli. -/
theorem instruction_mixtures :
    (1 / 2 < predictedSource .why ∧ 50 < observedSource .why) ∧
      predictedSource .whatNext < 1 / 2 ∧ observedSource .whatNext < 50 := by
  have hw : ∑ c, frequency .why c * sourceGiven c = 8363 := by decide
  have hn : ∑ c, frequency .whatNext c * sourceGiven c = 3136 := by decide
  refine ⟨⟨?_, by decide⟩, ?_, by decide⟩
  · rw [predictedSource, mixture_div, hw]; norm_num
  · rw [predictedSource, mixture_div, hn]; norm_num

/-! ### Bidirectionality (Table 6) -/

/-- Table 6: the frequency of a relation by prompt type. -/
def promptFrequency (p : Prompt) (c : CoherenceRelation) : ℕ :=
  pct [("table", "6"), ("prompt", p.tag), ("relation", relationTag c)] "frequency"

/-- The share of first mentions to the Goal by prompt type. -/
def goalMention (p : Prompt) : ℕ := pct [("table", "6"), ("prompt", p.tag)] "goalMention"

/-- An ambiguous pronoun is not inert: the prompt draws first mentions from the Goal to the
Source, the overlaid subject bias, and with them the continuations move from the Goal-biased
Occasion and Result toward the Source-biased Elaboration and Explanation, as (12) predicts. -/
theorem prompt_shifts_relations :
    goalMention .pronoun < goalMention .noPronoun ∧
      promptFrequency .noPronoun .elaboration + promptFrequency .noPronoun .explanation <
        promptFrequency .pronoun .elaboration + promptFrequency .pronoun .explanation ∧
      promptFrequency .pronoun .occasion + promptFrequency .pronoun .result <
        promptFrequency .noPronoun .occasion + promptFrequency .noPronoun .result := by
  decide

/-! ### The voice manipulation (Tables 7–10) -/

/-- Table 7: the rate of next mention of the causally implicated referent by voice and prompt. -/
def causalMention (v : Voice) (p : Prompt) : ℕ :=
  pct [("table", "7"), ("voice", voiceTag v), ("prompt", p.tag)] "causalMention"

/-- Table 8: the rate of Explanation continuations by voice and prompt. -/
def explanationRate (v : Voice) (p : Prompt) : ℕ :=
  pct [("table", "8"), ("voice", voiceTag v), ("prompt", p.tag)] "explanation"

/-- Table 9: the pronominalization rate of a position by voice, without a pronoun prompt. -/
def pronominalized (v : Voice) : Position → ℕ
  | .subject => pct [("table", "9"), ("voice", voiceTag v)] "subject"
  | .nonSubject => pct [("table", "9"), ("voice", voiceTag v)] "nonSubject"

/-- Table 10: the observed bias of the pronoun toward the subject by voice. -/
def actualSubject (v : Voice) : ℕ := pct [("table", "10"), ("voice", voiceTag v)] "actual"

/-- Table 7 without a pronoun prompt as the next-mention rate of the subject: the causally
implicated referent is the subject of the active and the by-phrase of the passive. -/
def subjectMention : Voice → ℕ
  | .Pass => 100 - causalMention .Pass .noPronoun
  | v => causalMention v .noPronoun

/-- The voice manipulation with the propositions constant: the pronoun refers to the causally
implicated referent less once the passive moves it out of subject position (Table 7), and the
continuations are Explanations less often (Table 8), the shift in coherence mediated by the shift
in reference. -/
theorem voice_shifts_interpretation_and_coherence :
    causalMention .Pass .pronoun < causalMention .Act .pronoun ∧
      explanationRate .Pass .pronoun < explanationRate .Act .pronoun := by
  decide

/-- (13) from Tables 7 and 9: the predicted bias of an ambiguous pronoun toward the subject. -/
def bayesSubject (v : Voice) : ℚ :=
  posterior
    (Position.select ((subjectMention v : ℚ) / 100) (((100 - subjectMention v : ℕ) : ℚ) / 100))
    (Position.select ((pronominalized v .subject : ℚ) / 100)
      ((pronominalized v .nonSubject : ℚ) / 100))
    .subject

private theorem posterior_select (s a b : ℕ) :
    posterior (Position.select ((s : ℚ) / 100) (((100 - s : ℕ) : ℚ) / 100))
        (Position.select ((a : ℚ) / 100) ((b : ℚ) / 100)) .subject =
      ((a * s : ℕ) : ℚ) / ((a * s + b * (100 - s) : ℕ) : ℚ) := by
  have hnum : (a : ℚ) / 100 * ((s : ℚ) / 100) = ((a * s : ℕ) : ℚ) / 10000 := by
    push_cast; ring
  have hden : (a : ℚ) / 100 * ((s : ℚ) / 100) + (b : ℚ) / 100 * (((100 - s : ℕ) : ℚ) / 100) =
      ((a * s + b * (100 - s) : ℕ) : ℚ) / 10000 := by
    push_cast; ring
  simp only [posterior, sum_position, Position.select]
  rw [hden, hnum, div_div_div_cancel_right₀ (by norm_num)]

/-- The Bayesian predictions of Table 10: from the next-mention rates without a pronoun (Table 7)
and the pronominalization rates (Table 9), the pronoun refers to the subject in both voices and
more strongly in the active, as the interpretations measured with the pronoun prompt show. -/
theorem voice_predictions :
    (1 / 2 < bayesSubject .Act ∧ 1 / 2 < bayesSubject .Pass ∧
        bayesSubject .Pass < bayesSubject .Act) ∧
      50 < actualSubject .Act ∧ 50 < actualSubject .Pass ∧
        actualSubject .Pass < actualSubject .Act := by
  have hA : subjectMention .Act = 59 := by decide
  have hP : subjectMention .Pass = 24 := by decide
  have haA : pronominalized .Act .subject = 62 := by decide
  have hbA : pronominalized .Act .nonSubject = 24 := by decide
  have haP : pronominalized .Pass .subject = 87 := by decide
  have hbP : pronominalized .Pass .nonSubject = 23 := by decide
  refine ⟨?_, by decide, by decide, by decide⟩
  simp only [bayesSubject, hA, hP, haA, hbA, haP, hbP]
  rw [posterior_select, posterior_select]
  norm_num

/-- The overlaid subject bias in the voice experiment: in both voices the subject is
pronominalized above the overall rate, so (13) puts the pronoun's bias toward it above its
next-mention prior, as the pronoun prompt's rise in subject mentions over the no-pronoun
condition shows for the active (Table 7). -/
theorem overlaid_subject_bias :
    ((subjectMention .Act : ℚ) / 100 < bayesSubject .Act ∧
        (subjectMention .Pass : ℚ) / 100 < bayesSubject .Pass) ∧
      causalMention .Act .noPronoun < causalMention .Act .pronoun := by
  have hA : subjectMention .Act = 59 := by decide
  have hP : subjectMention .Pass = 24 := by decide
  have haA : pronominalized .Act .subject = 62 := by decide
  have hbA : pronominalized .Act .nonSubject = 24 := by decide
  have haP : pronominalized .Pass .subject = 87 := by decide
  have hbP : pronominalized .Pass .nonSubject = 23 := by decide
  refine ⟨⟨?_, ?_⟩, by decide⟩ <;>
    simp only [bayesSubject, hA, hP, haA, hbA, haP, hbP] <;>
    exact (posterior_gt_iff (Position.select _ _) (Position.select _ _) .subject
      (by simp only [Position.select]; norm_num)
      (by rw [sum_position]; simp only [Position.select]; norm_num)).mpr
      (by rw [sum_position]; simp only [Position.select]; norm_num)

/-! ### Production tracks topichood, not expectancy -/

/-- How strongly a referent is signalled as the sentence topic: the subject of a passive,
promoted by a marked construction, more strongly than the subject of an active
([davison-1984]), and non-subjects not at all. -/
inductive TopichoodLevel where
  | low
  | default_
  | strong
  deriving DecidableEq, Repr, Fintype

def TopichoodLevel.rank : TopichoodLevel → Fin 3
  | .low => 0
  | .default_ => 1
  | .strong => 2

instance : LinearOrder TopichoodLevel := LinearOrder.lift' TopichoodLevel.rank (by decide)

/-- The topichood of a grammatical role by voice. -/
def topichood : Voice → GrammaticalRole → TopichoodLevel
  | .Pass, .subject => .strong
  | _, .subject => .default_
  | _, _ => .low

/-- Table 9 by grammatical role: the object of the active and the by-phrase of the passive are
the non-subjects. -/
def pronounRate (v : Voice) : GrammaticalRole → ℕ
  | .subject => pronominalized v .subject
  | _ => pronominalized v .nonSubject

/-- Production tracks topichood: across the voices and roles of Table 9 a higher topichood level
is pronominalized at a higher rate, the passive subject above the active subject above the
non-subjects, so not all grammatical subjects are equal. -/
theorem pronounRate_strictMono :
    ∀ v ∈ [Voice.Act, .Pass], ∀ v' ∈ [Voice.Act, .Pass], ∀ r r',
      topichood v r < topichood v' r' → pronounRate v r < pronounRate v' r' := by
  decide

/-- Production is not expectancy: without a pronoun prompt the passive's by-phrase referent is
mentioned next far more often than its subject, yet it is pronominalized far less: the rate of
pronominalization follows topichood, not the next-mention bias. -/
theorem production_not_expectancy :
    subjectMention .Pass < 100 - subjectMention .Pass ∧
      pronominalized .Pass .nonSubject < pronominalized .Pass .subject := by
  decide

/-! ### The design premise and the Centering term

The stimuli pair same-gender characters, so the prompt pronoun φ-agrees with both and the model
must decide between them; and under the grammatical-role ranking of forward-looking centers the
backward-looking center is the same in both voices, so the voice-induced gradient of Table 9
lives in the topichood term rather than in Centering's center. -/

/-- The two characters of (20), both third-person singular feminine. -/
def amanda : Word :=
  ⟨"Amanda", .PROPN, { person := some .third, number := some .Sing, gender := some .Fem }⟩

def brittany : Word :=
  ⟨"Brittany", .PROPN, { person := some .third, number := some .Sing, gender := some .Fem }⟩

/-- Both characters are candidate antecedents of the prompt *She*. -/
theorem she_ambiguous_over_stimuli :
    Proform.CandidateAntecedent English.Pronouns.she amanda ∧
      Proform.CandidateAntecedent English.Pronouns.she brittany := by
  decide

/-- The context sentence of (20a): Amanda the subject, Brittany the object. -/
def prevAmandaActive : Utterance Word GrammaticalRole :=
  { realizations := [⟨amanda, .subject, false⟩, ⟨brittany, .object, false⟩] }

/-- An active continuation pronominalizing both. -/
def curActive : Utterance Word GrammaticalRole :=
  { realizations := [⟨amanda, .subject, true⟩, ⟨brittany, .object, true⟩] }

/-- The passive continuation: Amanda promoted to subject, Brittany in the by-phrase. -/
def curPassive : Utterance Word GrammaticalRole :=
  { realizations := [⟨amanda, .subject, true⟩, ⟨brittany, .other, false⟩] }

/-- The backward-looking center is the same in both voices: the grammatical-role ranking does
not see voice. -/
theorem cb_invariant_under_voice :
    cb prevAmandaActive curActive = cb prevAmandaActive curPassive := by
  decide

/-- Topichood does see it. -/
theorem topichood_distinguishes_voice : topichood .Act .subject < topichood .Pass .subject := by
  decide

/-- The dissociation: Centering's center is voice-blind where the topichood term is
voice-sensitive, which is where the 87% against 62% of Table 9 lives. -/
theorem cb_topichood_dissociation_under_voice :
    cb prevAmandaActive curActive = cb prevAmandaActive curPassive ∧
      topichood .Act .subject < topichood .Pass .subject :=
  ⟨cb_invariant_under_voice, topichood_distinguishes_voice⟩

end KehlerRohde2013
