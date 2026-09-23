module

public import Linglib.Semantics.Questions.Bias
public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Semantics.Questions.Exhaustivity
public import Linglib.Semantics.Presupposition.Defs
public import Linglib.Discourse.CommonGround
public import Linglib.Logic.Modal.Defs
public import Linglib.Fragments.Slavic.Russian.QuestionParticles
public import Linglib.Fragments.Slavic.Bulgarian.QuestionParticles
public import Linglib.Fragments.Slavic.Ukrainian.QuestionParticles
public import Linglib.Fragments.Slavic.Polish.QuestionParticles
public import Linglib.Fragments.Slavic.Slovenian.QuestionParticles
public import Linglib.Fragments.Slavic.Serbian.QuestionParticles
public import Linglib.Fragments.Slavic.Macedonian.QuestionParticles
public import Linglib.Fragments.Slavic.Czech.Particles
public import Linglib.Data.Examples.Simik2024

/-!
# Šimík (2024): Polar question semantics and bias: Lessons from Slavic/Czech

This file formalizes [simik-2024]'s survey of polar-question bias in Slavic. A question
form's bias profile is the set of cells, contextual evidence by prior epistemic bias
([sudo-2013]), in which it is felicitous: Table 2 gives the profile of the four Czech forms,
interrogative and declarative crossed with polarity (`czechBiasProfile`), and Table 1 the
profile of the Serbian strategies reported from [todorovic-2023] (`serbianBiasProfile`).
The Czech cleaning-service scenarios (11)–(18) are typed rows, and the table predicts each
judgment (`cleaning_examples_match_table2`); declaratives need evidence
(`declarative_requires_evidence`) and Czech InterNPQ, unlike English high negation, is
felicitous under positive evidence (`interNPQ_broader_than_english_hiNQ`), while Serbian
high negation is narrower than English (`serbian_hnpq_narrower_than_english`). The quiz
scenario (24) diagnoses each of ten languages' default strategy: its positive form is the
quiz-felicitous one (`default_quiz_felicitous`), declaratives never are
(`declarative_quiz_infelicitous`), and negation triggers bias except under Polish *czy*
and Macedonian *dali* (`negationTriggersBias_iff`). Serbian *je li* is neutral in Table 1 yet
quiz-infelicitous (`jeLi_neutral_yet_quiz_infelicitous`), the contrast the chapter
attributes to a covert 'wonder' selecting the question (`wonderLF`), which denotes the
unique true answer (`trueAnswers_polar_existsUnique`). Russian *razve* resolves a conflict
between evidence for the prejacent and a prior against it (`razveProfile`), invariantly
across inner and outer negation (`razveProfile_negation_invariant`), and is a root
phenomenon while *li* embeds (`razve_root_li_embedded`). The chapter's Czech FALSUM
(`falsumCz`) presupposes only epistemic possibility of the prejacent, weaker than
[repp-2013]'s operator (`falsum`, `assertion_of_falsum`), and licenses the particle
*náhodou* under outer negation alone (`NahodouLicensed`, `nahodou_examples`).

## Implementation notes

Table 2's starred DeclPPQ of the neutral cell, conditioned on a contrastive topic, is
admitted by `czechFelicitous` and read off the row feature `contrastiveTopic`. The
language rows carry the paper's own strategy labels; the derived predicates read the
normalized `strategy` and `polarity` features. The kin of *razve* across Slavic are listed
(`razveKin`) without a profile, as the chapter leaves their semantics open.

## References

* [simik-2024]
* [sudo-2013], [buring-gunlogson-2000], [romero-han-2004], [gartner-gyuris-2017]
* [romero-2024], [repp-2013], [repp-geist-2022], [korotkova-2023]
* [todorovic-2023], [stankova-2023], [esipova-romero-2023]
* [hamblin-1973b], [karttunen-1977], [dayal-1996]
-/

@[expose] public section

namespace Simik2024

open Question Data.Examples

/-! ### Bias and the polarity of the prejacent (§3.1) -/

/-- The contextual evidence a conflict-resolving question of the given polarity rests on:
evidence for the prejacent as asked. -/
def evidence : Polarity → ContextualEvidence
  | .positive => .forP
  | .negative => .againstP

/-- The prior epistemic bias a conflict-resolving question of the given polarity
double-checks: against the prejacent as asked. -/
def prior : Polarity → OriginalBias
  | .positive => .againstP
  | .negative => .forP

/-- The polarity of a [romero-2024] question form. -/
def polarityOf : PQForm → Polarity
  | .PosQ => .positive
  | .LoNQ | .HiNQ => .negative

/-! ### The Czech forms and their bias profile (§3.2, Table 2) -/

/-- The chapter's grid of Czech polar-question forms: interrogative (verb-initial) or
declarative word order, crossed with polarity. -/
inductive CzechPQForm
  | interPPQ
  | interNPQ
  | declPPQ
  | declNPQ
  deriving DecidableEq, Repr, Fintype

/-- The [romero-2024] form of each grid cell: InterNPQ is high negation, DeclNPQ low. -/
def CzechPQForm.toPQForm : CzechPQForm → PQForm
  | .interPPQ | .declPPQ => .PosQ
  | .interNPQ => .HiNQ
  | .declNPQ => .LoNQ

/-- Declarative word order. -/
def CzechPQForm.Declarative : CzechPQForm → Prop
  | .declPPQ | .declNPQ => True
  | .interPPQ | .interNPQ => False

instance : DecidablePred CzechPQForm.Declarative := fun f => by
  cases f <;> simp only [CzechPQForm.Declarative] <;> infer_instance

/-- Table 2: the forms natural in each cell of contextual evidence by prior epistemic
bias, the starred DeclPPQ of the neutral cell left to `czechFelicitous`. -/
def czechBiasProfile : ContextualEvidence → OriginalBias → Finset CzechPQForm
  | .forP, .forP => ∅
  | .forP, .neutral => {.declPPQ, .interNPQ}
  | .forP, .againstP => {.declPPQ}
  | .neutral, .forP => {.interPPQ, .interNPQ}
  | .neutral, .neutral => {.interPPQ}
  | .neutral, .againstP => ∅
  | .againstP, .forP => {.declNPQ, .interNPQ}
  | .againstP, .neutral => {.declNPQ}
  | .againstP, .againstP => ∅

/-- The forms felicitous in a cell, admitting the unbiased declarative of (18) when a
contrastive topic claims the initial position. -/
def czechFelicitous (ev : ContextualEvidence) (ob : OriginalBias) (ct : Bool) :
    Finset CzechPQForm :=
  if ct ∧ ev = .neutral ∧ ob = .neutral then insert .declPPQ (czechBiasProfile ev ob)
  else czechBiasProfile ev ob

variable (ev : ContextualEvidence) (ob : OriginalBias)

/-- The default form is natural exactly without evidence and without a prior against
the prejacent. -/
theorem interPPQ_mem_iff :
    .interPPQ ∈ czechBiasProfile ev ob ↔ ev = .neutral ∧ ob ≠ .againstP := by
  cases ev <;> cases ob <;> decide

/-- DeclPPQ needs positive evidence and no prior for the prejacent. -/
theorem declPPQ_mem_iff :
    .declPPQ ∈ czechBiasProfile ev ob ↔ ev = .forP ∧ ob ≠ .forP := by
  cases ev <;> cases ob <;> decide

/-- DeclNPQ needs negative evidence and no prior against the prejacent. -/
theorem declNPQ_mem_iff :
    .declNPQ ∈ czechBiasProfile ev ob ↔ ev = .againstP ∧ ob ≠ .againstP := by
  cases ev <;> cases ob <;> decide

/-- InterNPQ conveys a prior for the prejacent, with neutral or conflicting evidence, or
else positive evidence without a prior (the explanation-seeking (17)). -/
theorem interNPQ_mem_iff :
    .interNPQ ∈ czechBiasProfile ev ob ↔
      ob = .forP ∧ ev ≠ .forP ∨ ev = .forP ∧ ob = .neutral := by
  cases ev <;> cases ob <;> decide

/-- Declarative questions are specialized for evidential bias ([gunlogson-2002]). -/
theorem declarative_requires_evidence (f : CzechPQForm) (hf : f.Declarative)
    (h : f ∈ czechBiasProfile ev ob) : ev ≠ .neutral := by
  revert hf h; cases f <;> cases ev <;> cases ob <;> decide

/-- Czech high negation is broader than English: felicitous under positive evidence,
which [romero-2024]'s table excludes. -/
theorem interNPQ_broader_than_english_hiNQ :
    .interNPQ ∈ czechBiasProfile .forP .neutral ∧ evidenceBiasOK .HiNQ .forP = false :=
  ⟨by decide, rfl⟩

/-! ### The cleaning scenarios (11)–(18) -/

/-- The grid form a row instantiates. -/
def form? (e : LinguisticExample) : Option CzechPQForm :=
  e.parse? "form"
    [("interPPQ", .interPPQ), ("interNPQ", .interNPQ), ("declPPQ", .declPPQ),
     ("declNPQ", .declNPQ)]

/-- The contextual evidence of a row's scenario. -/
def evidence? (e : LinguisticExample) : Option ContextualEvidence :=
  e.parse? "evidence" [("forP", .forP), ("neutral", .neutral), ("againstP", .againstP)]

/-- The speaker's prior epistemic bias in a row's scenario. -/
def epistemic? (e : LinguisticExample) : Option OriginalBias :=
  e.parse? "epistemic" [("forP", .forP), ("neutral", .neutral), ("againstP", .againstP)]

/-- Whether a row's scenario places a contrastive topic clause-initially. -/
def contrastiveTopic (e : LinguisticExample) : Bool :=
  e.feature? "contrastiveTopic" == some "true"

/-- Table 2 predicts the scenarios: a form is judged infelicitous exactly when its cell
excludes it, the degraded InterPPQ of (18) counting as admitted. -/
theorem cleaning_examples_match_table2 :
    ∀ e ∈ Examples.all, ∀ f ∈ form? e, ∀ ev ∈ evidence? e, ∀ ob ∈ epistemic? e,
      e.judgment = .unacceptable ↔ f ∉ czechFelicitous ev ob (contrastiveTopic e) := by
  decide

/-! ### Default strategies under the quiz scenario (§4.1) -/

/-- The ten surveyed languages. -/
inductive Language
  | czech
  | slovak
  | upperSorbian
  | slovenian
  | ukrainian
  | polish
  | serbian
  | macedonian
  | bulgarian
  | russian
  deriving DecidableEq, Repr, Fintype

/-- Glottocode, the key of the example rows. -/
def Language.glottocode : Language → String
  | .czech => "czec1258"
  | .slovak => "slov1269"
  | .upperSorbian => "uppe1395"
  | .slovenian => "slov1268"
  | .ukrainian => "ukra1253"
  | .polish => "poli1260"
  | .serbian => "serb1264"
  | .macedonian => "mace1250"
  | .bulgarian => "bulg1262"
  | .russian => "russ1263"

/-- The formal means of marking a polar question. -/
inductive Strategy
  | verbMovement
  | clauseInitialParticle
  | verbAttachedParticle
  | declarative
  | intonation
  deriving DecidableEq, Repr, Fintype

/-- The chapter's summary classification of each language's default strategy: verb or
auxiliary movement, an utterance-initial particle, or a verb-attached particle. -/
def Language.defaultStrategy : Language → Strategy
  | .czech | .slovak | .upperSorbian | .slovenian => .verbMovement
  | .ukrainian | .polish | .serbian | .macedonian => .clauseInitialParticle
  | .bulgarian | .russian => .verbAttachedParticle

/-- The question particles of each language's fragment. -/
def Language.particles : Language → List Particle
  | .czech | .slovak | .upperSorbian => []
  | .slovenian =>
    [Slovenian.QuestionParticles.ali, Slovenian.QuestionParticles.a,
     Slovenian.QuestionParticles.kaj]
  | .ukrainian => [Ukrainian.QuestionParticles.cy, Ukrainian.QuestionParticles.xiba]
  | .polish => [Polish.QuestionParticles.czy, Polish.QuestionParticles.czyzby]
  | .serbian =>
    [Serbian.QuestionParticles.li, Serbian.QuestionParticles.daLi,
     Serbian.QuestionParticles.jeLi, Serbian.QuestionParticles.zar]
  | .macedonian =>
    [Macedonian.QuestionParticles.dali, Macedonian.QuestionParticles.li,
     Macedonian.QuestionParticles.zar]
  | .bulgarian => [Bulgarian.QuestionParticles.li, Bulgarian.QuestionParticles.nima]
  | .russian =>
    [Russian.QuestionParticles.li, Russian.QuestionParticles.razve,
     Russian.QuestionParticles.neuzeli]

/-- The strategy a quiz row instantiates. -/
def strategy? (e : LinguisticExample) : Option Strategy :=
  e.parse? "strategy"
    [("verbMovement", .verbMovement), ("clauseInitialParticle", .clauseInitialParticle),
     ("verbAttachedParticle", .verbAttachedParticle), ("declarative", .declarative),
     ("intonation", .intonation)]

/-- The polarity of a quiz row. -/
def polarity? (e : LinguisticExample) : Option Polarity :=
  e.parse? "polarity" [("positive", .positive), ("negative", .negative)]

/-- The quiz rows (25)–(34) of a language. -/
def quizRows (l : Language) : List LinguisticExample :=
  Examples.all.filter fun e => e.language == l.glottocode && (e.feature? "strategy").isSome

variable (l : Language)

/-- Every language's default strategy is quiz-felicitous in its positive form. -/
theorem default_quiz_felicitous :
    ∃ e ∈ quizRows l, strategy? e = some l.defaultStrategy ∧ polarity? e = some .positive ∧
      e.judgment = .acceptable := by
  cases l <;> decide

/-- Declarative polar questions convey evidential bias and are quiz-infelicitous in every
language. -/
theorem declarative_quiz_infelicitous :
    ∀ e ∈ Examples.all, strategy? e = some .declarative → e.judgment = .unacceptable := by
  decide

/-- Negation triggers bias in a language when no negated interrogative form is
quiz-felicitous. -/
def NegationTriggersBias : Prop :=
  ∀ e ∈ quizRows l, polarity? e = some .negative → strategy? e ≠ some .declarative →
    e.judgment ≠ .acceptable

instance : Decidable (NegationTriggersBias l) := by
  unfold NegationTriggersBias; infer_instance

/-- Every language's quiz rows include a negated interrogative form. -/
theorem negated_interrogative_attested :
    ∃ e ∈ quizRows l, polarity? e = some .negative ∧ strategy? e ≠ some .declarative := by
  cases l <;> decide

/-- Negation triggers bias everywhere except under Polish *czy* (30b) and Macedonian
*dali* (32a). -/
theorem negationTriggersBias_iff :
    NegationTriggersBias l ↔ l ≠ .polish ∧ l ≠ .macedonian := by
  cases l <;> decide

/-- The particle of every quiz row is an entry of the language's fragment. -/
theorem quiz_particles_in_fragment :
    ∀ e ∈ quizRows l, ∀ f ∈ e.feature? "particle", f ∈ l.particles.map (·.form) := by
  cases l <;> decide

/-- Every fragment particle is recorded in matrix polar questions. -/
theorem particles_licensed_polar : ∀ p ∈ l.particles, p.Licensed .polar .matrix := by
  cases l <;> decide

/-! ### The Serbian strategies and Todorović's bias profile (§4.2.2, Table 1) -/

/-- The Serbian strategies of (31) and Table 1: the two positive particle strategies,
high negation (*nije li*) and low negation (*je l' … nije*). -/
inductive SerbianPQForm
  | daLiPPQ
  | jeLiPPQ
  | hnpq
  | lnpq
  deriving DecidableEq, Repr, Fintype

/-- The fragment marker of each strategy. -/
def SerbianPQForm.particle : SerbianPQForm → Particle
  | .daLiPPQ => Serbian.QuestionParticles.daLi
  | .jeLiPPQ | .lnpq => Serbian.QuestionParticles.jeLi
  | .hnpq => Serbian.QuestionParticles.li

/-- The [romero-2024] form of each strategy. -/
def SerbianPQForm.toPQForm : SerbianPQForm → PQForm
  | .daLiPPQ | .jeLiPPQ => .PosQ
  | .hnpq => .HiNQ
  | .lnpq => .LoNQ

/-- Table 1: the Serbian strategies natural in each cell, after [todorovic-2023]. -/
def serbianBiasProfile : ContextualEvidence → OriginalBias → Finset SerbianPQForm
  | .forP, .forP => ∅
  | .forP, .neutral => {.jeLiPPQ}
  | .forP, .againstP => ∅
  | .neutral, .forP => {.jeLiPPQ}
  | .neutral, .neutral => {.daLiPPQ, .jeLiPPQ}
  | .neutral, .againstP => {.lnpq}
  | .againstP, .forP => {.lnpq, .hnpq}
  | .againstP, .neutral => {.lnpq}
  | .againstP, .againstP => ∅

/-- *da li* questions are limited to neutral contexts. -/
theorem daLiPPQ_mem_iff :
    .daLiPPQ ∈ serbianBiasProfile ev ob ↔ ev = .neutral ∧ ob = .neutral := by
  cases ev <;> cases ob <;> decide

/-- *je li* questions have the broader distribution. -/
theorem jeLiPPQ_of_daLiPPQ (h : .daLiPPQ ∈ serbianBiasProfile ev ob) :
    .jeLiPPQ ∈ serbianBiasProfile ev ob := by
  revert h; cases ev <;> cases ob <;> decide

/-- Positive questions are incompatible with negative biases. -/
theorem ppq_no_negative_bias (f : SerbianPQForm) (hf : f.toPQForm = .PosQ)
    (h : f ∈ serbianBiasProfile ev ob) : ev ≠ .againstP ∧ ob ≠ .againstP := by
  revert hf h; cases f <;> cases ev <;> cases ob <;> decide

/-- High negation resolves a conflict between a prior for the prejacent and evidence
against it, and nothing else. -/
theorem hnpq_mem_iff :
    .hnpq ∈ serbianBiasProfile ev ob ↔ ev = .againstP ∧ ob = .forP := by
  cases ev <;> cases ob <;> decide

/-- Low negation has the broader distribution among negative questions. -/
theorem lnpq_of_hnpq (h : .hnpq ∈ serbianBiasProfile ev ob) :
    .lnpq ∈ serbianBiasProfile ev ob := by
  revert h; cases ev <;> cases ob <;> decide

/-- Serbian high negation is narrower than English: the suggestion scenarios of
[romero-2024]'s table, neutral evidence, admit no Serbian HNPQ. -/
theorem serbian_hnpq_narrower_than_english :
    evidenceBiasOK .HiNQ .neutral = true ∧ ∀ ob, .hnpq ∉ serbianBiasProfile .neutral ob :=
  ⟨rfl, fun ob => by cases ob <;> decide⟩

/-- The quiz rows of (31) carry the markers of the Table 1 strategies. -/
theorem ex31_markers :
    Examples.ex31a.feature? "particle" = some SerbianPQForm.daLiPPQ.particle.form ∧
    Examples.ex31b.feature? "particle" = some SerbianPQForm.jeLiPPQ.particle.form ∧
    Examples.ex31c.feature? "particle" = some SerbianPQForm.hnpq.particle.form ∧
    Examples.ex31d.feature? "particle" = some SerbianPQForm.lnpq.particle.form := by
  decide

/-- The quiz-versus-information-seeking contrast: *je li* is natural in the neutral cell
of Table 1 yet infelicitous in the quiz (31b), where *da li* is felicitous (31a). -/
theorem jeLi_neutral_yet_quiz_infelicitous :
    .jeLiPPQ ∈ serbianBiasProfile .neutral .neutral ∧
      Examples.ex31b.judgment = .unacceptable ∧ Examples.ex31a.judgment = .acceptable := by
  decide

/-! ### Information-seeking questions (§2, §4.2.1)

The chapter hypothesizes that the strategies that are neutral yet quiz-infelicitous
(Serbian *je li*, Slovenian *a*, possibly Russian intonation questions) embed the Hamblin
question under a covert 'wonder', modelled as 'want to know' applied to the true answer
([karttunen-1977], [dayal-1996]); a quiz master knows the answer and so cannot want to
know it. -/

section Wonder

variable {W : Type*} (p : Set W) (w : W)

/-- A polar question has exactly one true answer at each world. -/
theorem trueAnswers_polar_existsUnique : ∃! q, q ∈ trueAnswers {p, pᶜ} w := by
  by_cases hw : w ∈ p
  · refine ⟨p, ⟨by simp, hw⟩, fun q ⟨hq, hwq⟩ => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · rfl
    · exact absurd hw hwq
  · refine ⟨pᶜ, ⟨by simp, hw⟩, fun q ⟨hq, hwq⟩ => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact absurd hwq hw
    · rfl

/-- The chapter's (36): the speaker wants to know the true answer to the polar question
over `p`; the embedded (10b) is the same form with the attitude holder in place of the
speaker. -/
def wonderLF {E : Type*} (wantToKnow : E → Set W → Set W) (x : E) : Set W :=
  {w | ∃ q ∈ trueAnswers {p, pᶜ} w, w ∈ wantToKnow x q}

end Wonder

/-! ### Russian *razve* and its kin (§4.2.4) -/

/-- The bias profile of a *razve* question by form: evidence for the prejacent as asked
against a prior for its negation (the conflict-resolving profile of §3.1). -/
def razveProfile (f : PQForm) : ContextualEvidence × OriginalBias :=
  (evidence (polarityOf f), prior (polarityOf f))

/-- The profile of *razve* negative questions is the same under inner negation (VERUM)
and outer negation (FALSUM): negative evidence, positive prior. -/
theorem razveProfile_negation_invariant :
    razveProfile .LoNQ = razveProfile .HiNQ ∧ razveProfile .HiNQ = (.againstP, .forP) :=
  ⟨rfl, rfl⟩

/-- *Razve* is compatible with both negations ([repp-geist-2022]'s LFs (40), diagnosed
by the polarity items in (41)), *neuželi* with inner negation only. -/
def razveNegations : Finset PQForm := {.LoNQ, .HiNQ}

/-- *Neuželi* lexicalizes VERUM and so tolerates inner negation only. -/
def neuzeliNegations : Finset PQForm := {.LoNQ}

theorem neuzeliNegations_ssubset : neuzeliNegations ⊂ razveNegations := by decide

/-- *Razve* is a root phenomenon while *li* is obligatory in subordinated polar questions
([korotkova-2023]), read off the fragment cells. -/
theorem razve_root_li_embedded :
    ¬ Russian.QuestionParticles.razve.LicensedInEmbed .subordinated ∧
      Russian.QuestionParticles.li.Licensed .polar .subordinated := by
  decide

/-- The kin of *razve* the chapter lists across Slavic, whose semantics it leaves open. -/
def razveKin : List Particle :=
  [Ukrainian.QuestionParticles.xiba, Polish.QuestionParticles.czyzby,
   Bulgarian.QuestionParticles.nima, Macedonian.QuestionParticles.zar,
   Serbian.QuestionParticles.zar, Czech.Particles.copak]

/-! ### FALSUM and the Czech outer negation (§3.3.2, §5) -/

section Falsum

variable {W : Type*} (epi conv : W → W → Prop) (cg : W → Filter W) (p : Set W)

/-- [repp-2013]'s FALSUM (22b): at every world compatible with the bearer's knowledge and
every world compatible with their conversational goals, the proposition is not in the
common ground. -/
def falsum : Set W := ModalLogic.box epi (ModalLogic.box conv fun w => p ∉ cg w)

/-- The chapter's Czech FALSUM (44): defined when the attitude holder considers the
prejacent possible, and true when it is not in the common ground. -/
def falsumCz : Presupposition.PartialProp W where
  presup := ModalLogic.diamond epi (· ∈ p)
  assertion := fun w => p ∉ cg w

/-- The question (45) over the Czech FALSUM: whether the prejacent is outside the common
ground. -/
def falsumCzQuestion : Question W := polar {w | p ∉ cg w}

/-- The commitment of the Czech operator is weak: its presupposition is epistemic
possibility, the dual of necessity. -/
theorem falsumCz_presup_iff (w : W) :
    (falsumCz epi cg p).presup w ↔ ¬ ModalLogic.box epi (· ∉ p) w := by
  simp [falsumCz, ModalLogic.box, ModalLogic.diamond]

/-- Under reflexive accessibilities [repp-2013]'s operator entails the Czech assertion. -/
theorem assertion_of_falsum [Std.Refl epi] [Std.Refl conv] {w : W}
    (h : w ∈ falsum epi conv cg p) : (falsumCz epi cg p).assertion w :=
  h w (Std.Refl.refl w) w (Std.Refl.refl w)

end Falsum

/-- The two readings of negation in a polar question (the chapter's (14), after
[ladd-1981] and [repp-2013]): inner negation is the classical propositional operator,
diagnosed by negative polarity items; outer negation is the non-propositional operator
FALSUM, diagnosed by positive polarity items. -/
inductive Negation
  | inner
  | outer
  deriving DecidableEq, Repr, Fintype

/-- *Náhodou* is licensed by outer negation and by nothing else (43). -/
def NahodouLicensed (pol : Polarity) (n : Negation) : Prop :=
  pol = .negative ∧ n = .outer

instance (pol : Polarity) (n : Negation) : Decidable (NahodouLicensed pol n) := by
  unfold NahodouLicensed; infer_instance

/-- *Náhodou* needs negation (43e). -/
theorem nahodou_requires_negation (n : Negation) : ¬ NahodouLicensed .positive n :=
  fun h => Polarity.noConfusion h.1

/-- *Náhodou* needs outer negation (43d). -/
theorem nahodou_requires_outer (pol : Polarity) (n : Negation)
    (h : NahodouLicensed pol n) : n = .outer := h.2

/-- The negation reading an indefinite diagnoses: the polarity item outer, the concord
item inner. -/
def indefiniteNegation? (e : LinguisticExample) : Option Negation :=
  e.parse? "indefinite" [("ppi", .outer), ("nci", .inner)]

/-- The (43) rows with *náhodou* are acceptable exactly when the particle is licensed by
the polarity and the reading the indefinite diagnoses. -/
theorem nahodou_examples :
    ∀ e ∈ Examples.all, e.feature? "nahodou" = some "true" →
      ∀ pol ∈ polarity? e, ∀ n ∈ indefiniteNegation? e,
        (e.judgment = .acceptable ↔ NahodouLicensed pol n) := by
  decide

end Simik2024
