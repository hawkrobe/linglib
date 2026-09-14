import Linglib.Fragments.Slavic.Czech.Particles
import Linglib.Fragments.Slavic.Czech.Determiners
import Linglib.Semantics.Polarity.CzechNegation
import Linglib.Semantics.Questions.Bias
import Linglib.Logic.Modal.Defs

/-!
# Staňková and Šimík (2025): Negation in Czech Polar Questions

This file formalizes [stankova-2025]'s analysis of negation in Czech polar questions. The
negative prefix moves with the finite verb, so verb position fixes the position of negation:
a clause-initial verb sits above the canonical negation operator and can only be licensed by
the commitment operator FALSUM of [repp-2013] (`falsum`), while a verb in situ is licensed
either by the operator or by FALSUM (`mem_availableReadings_iff`). Inner negation licenses
negative concord items and is tied to negative contextual evidence; FALSUM allows positive
polarity items and conveys weak epistemic bias, indifferent to contextual evidence; and
declarative word order requires contextual evidence ([gunlogson-2002]). Felicity of a
question in a context follows from these three sources (`Felicitous`), which yields the
predictions the paper's naturalness study tests: in interrogative questions the positive
polarity item is felicitous in every context and the negative concord item in none
(`v1_ppi_any_context`, `v1_nci_never`, `v1_context_invariant`), and declarative questions
need contextual evidence, the concord item negative evidence and the polarity item any
evidence (`nonV1_nci_iff`, `nonV1_ppi_iff`, `nonV1_neutral_infelicitous`). Czech FALSUM is
thereby broader than English high negation, felicitous even with positive evidence
(`falsum_broader_than_english_hiNQ`). The particle *náhodou* is licensed by FALSUM alone, so
it excludes concord items and needs negation whatever the word order
(`nahodou_excludes_nci`, `nahodou_requires_negation`), and *copak* needs contextual evidence
matching the question's polarity, against the speaker's prior belief (`copak_requires_bias`,
`copak_prior_ne_evidence`); the two particles part on context sensitivity
(`nahodou_copak_opposite`).

## Implementation notes

The main experiment (seventy-five speakers, a fully crossed design of verb position,
indefinite and context, cumulative link mixed models) found a main effect of the indefinite
in interrogative questions, no effect of context there, a preference for negative contexts
and for concord items in declarative questions, high naturalness of interrogative questions
under positive evidence, a main effect of the indefinite for *náhodou* questions, and a
main effect of context for *copak* questions; these results are stated in prose only. The
three-way negation of [stankova-2026] supplies the substrate's medial reading, which this
paper does not distinguish from inner negation; the substrate's evidential bias strengths
fix the evidence each reading requires.

## References

* [stankova-2025]
* [repp-2013]
* [zeijlstra-2004]
* [sudo-2013]
* [gartner-gyuris-2017]
* [nekula-1996]
* [simik-2024]
-/

namespace StankovaSimik2025

open Czech.Particles (nahodou copak)
open Czech.Determiners (zadny nejaky)
open Czech.Negation
open Question

/-! ### FALSUM -/

section Falsum

variable {W : Type*} (epi conv : W → W → Prop) (cg : W → Set (Set W)) (p : Set W)

/-- The FALSUM operator (the paper's (7)): at every world compatible with the bearer's
knowledge, at every world compatible with their conversational goals, the proposition is
not in the common ground. -/
def falsum : Set W := {w | ∀ w', epi w w' → ∀ w'', conv w' w'' → p ∉ cg w''}

/-- FALSUM is a necessity nested in a necessity. -/
theorem falsum_eq_box_box :
    falsum epi conv cg p = ModalLogic.box epi (ModalLogic.box conv λ w => p ∉ cg w) := rfl

end Falsum

/-! ### Verb position and the readings of negation -/

/-- Verb position in a Czech polar question: clause-initial (interrogative word order) or in
situ (declarative word order). The negative prefix is inseparable from the finite verb, so verb
position fixes the position of negation. -/
inductive VerbPosition
  | v1
  | nonV1
  deriving DecidableEq, Repr, Fintype

/-- The height of the negated verb, in the coordinates of the negation positions: the
clause-initial verb raises above the canonical negation operator into the region FALSUM
c-commands, the verb in situ stays in TP (the paper's (11) and (12)). -/
def VerbPosition.verbHeight : VerbPosition → ℕ
  | .v1 => Position.outer.toNat
  | .nonV1 => Position.inner.toNat

/-- The readings of negation available at a verb position: the clause-initial verb is
licensed by FALSUM alone, the verb in situ by FALSUM or by the canonical operator. -/
def VerbPosition.availableReadings : VerbPosition → List Position
  | .v1 => [.outer]
  | .nonV1 => [.inner, .medial, .outer]

/-- A reading is available exactly when its operator c-commands the negated verb, that is,
sits at or above it. -/
theorem mem_availableReadings_iff (wp : VerbPosition) (pos : Position) :
    pos ∈ wp.availableReadings ↔ wp.verbHeight ≤ pos.toNat := by
  cases wp <;> cases pos <;> decide

/-- The unmarked reading at a verb position: the lowest available operator. -/
def VerbPosition.defaultReading : VerbPosition → Position
  | .v1 => .outer
  | .nonV1 => .inner

theorem defaultReading_eq_min (wp : VerbPosition) :
    wp.availableReadings.min? = some wp.defaultReading := by
  cases wp <;> decide

/-! ### Indefinites as proxies for the readings -/

/-- The indefinite manipulated in the experiment: the negative concord item *žádný*, a proxy
for inner negation, or the positive polarity item *nějaký*, a proxy for FALSUM. -/
inductive Indefinite
  | nci
  | ppi
  deriving DecidableEq, Repr, Fintype

/-- The determiner entry realizing each indefinite. -/
def Indefinite.entry : Indefinite → Czech.Determiners.DetEntry
  | .nci => zadny
  | .ppi => nejaky

/-- The licensing diagnostic each indefinite tests. -/
def Indefinite.diagnostic : Indefinite → Diagnostic
  | .nci => .nciLicensed
  | .ppi => .ppiOutscoping

/-- Each indefinite tests the diagnostic its lexical entry carries. -/
theorem indefinite_diagnostic_matches_lexicon (ind : Indefinite) :
    ind.entry.diagnostic = some ind.diagnostic := by
  cases ind <;> rfl

/-- The concord item is licensed by inner negation alone, through Agree with the canonical
operator ([zeijlstra-2004]). -/
theorem nci_licensed_iff (pos : Position) : licenses pos .nciLicensed = true ↔ pos = .inner := by
  cases pos <;> decide

/-! ### Bias and felicity -/

/-- The contextual evidence a reading of negation requires: inner negation, with strong
evidential bias, negative evidence; medial negation, with weak bias, no positive evidence;
FALSUM, with no evidential bias, nothing. -/
def readingEvidenceOK (pos : Position) (ctx : ContextualEvidence) : Prop :=
  match pos.biasStrength with
  | .strong => ctx = .againstP
  | .weak => ctx ≠ .forP
  | .none_ => True

instance (pos : Position) (ctx : ContextualEvidence) : Decidable (readingEvidenceOK pos ctx) := by
  cases pos <;> simp only [readingEvidenceOK, Position.biasStrength] <;> infer_instance

/-- Declarative word order requires contextual evidence ([gunlogson-2002]); interrogative
word order requires none. -/
def wordOrderEvidenceOK : VerbPosition → ContextualEvidence → Prop
  | .v1, _ => True
  | .nonV1, ctx => ctx ≠ .neutral

instance (wp : VerbPosition) (ctx : ContextualEvidence) :
    Decidable (wordOrderEvidenceOK wp ctx) := by
  cases wp <;> unfold wordOrderEvidenceOK <;> infer_instance

/-- A negative polar question with an indefinite is felicitous in a context when some reading
available at its verb position licenses the indefinite and admits the context's evidence, and
the word order admits the evidence. -/
def Felicitous (wp : VerbPosition) (ind : Indefinite) (ctx : ContextualEvidence) : Prop :=
  (∃ pos ∈ wp.availableReadings, licenses pos ind.diagnostic = true ∧
    readingEvidenceOK pos ctx) ∧ wordOrderEvidenceOK wp ctx

instance (wp : VerbPosition) (ind : Indefinite) (ctx : ContextualEvidence) :
    Decidable (Felicitous wp ind ctx) := by
  unfold Felicitous; infer_instance

/-- In interrogative questions the positive polarity item is felicitous in every context:
FALSUM licenses it and is indifferent to evidence. -/
theorem v1_ppi_any_context (ctx : ContextualEvidence) : Felicitous .v1 .ppi ctx := by
  cases ctx <;> decide

/-- In interrogative questions the negative concord item is never felicitous: the
clause-initial verb is out of reach of the canonical operator. -/
theorem v1_nci_never (ctx : ContextualEvidence) : ¬ Felicitous .v1 .nci ctx := by
  cases ctx <;> decide

/-- Interrogative questions are indifferent to the context. -/
theorem v1_context_invariant (ind : Indefinite) (ctx ctx' : ContextualEvidence) :
    Felicitous .v1 ind ctx ↔ Felicitous .v1 ind ctx' := by
  cases ind <;> cases ctx <;> cases ctx' <;> decide

/-- A declarative question with the concord item is felicitous exactly under negative
evidence: inner negation requires it. -/
theorem nonV1_nci_iff (ctx : ContextualEvidence) :
    Felicitous .nonV1 .nci ctx ↔ ctx = .againstP := by
  cases ctx <;> decide

/-- A declarative question with the polarity item is felicitous exactly under some evidence:
FALSUM licenses the verb in situ, and the word order needs evidence. -/
theorem nonV1_ppi_iff (ctx : ContextualEvidence) :
    Felicitous .nonV1 .ppi ctx ↔ ctx ≠ .neutral := by
  cases ctx <;> decide

/-- Declarative questions are infelicitous without contextual evidence. -/
theorem nonV1_neutral_infelicitous (ind : Indefinite) : ¬ Felicitous .nonV1 ind .neutral := by
  cases ind <;> decide

/-- Czech FALSUM is broader than English high negation: an interrogative question with the
polarity item is felicitous under positive evidence (the paper's (14)), which the English
form excludes ([gartner-gyuris-2017]). -/
theorem falsum_broader_than_english_hiNQ :
    evidenceBiasOK .HiNQ .forP = false ∧ Felicitous .v1 .ppi .forP :=
  ⟨rfl, v1_ppi_any_context .forP⟩

/-! ### The particles -/

/-- The polarity of a polar question. -/
inductive Polarity
  | positive
  | negative
  deriving DecidableEq, Repr, Fintype

/-- *Náhodou* is licensed by FALSUM: it is felicitous with a reading of negation exactly when
that reading is outer. -/
def NahodouLicensed (pol : Polarity) (pos : Position) : Prop := pol = .negative ∧ pos = .outer

instance (pol : Polarity) (pos : Position) : Decidable (NahodouLicensed pol pos) := by
  unfold NahodouLicensed; infer_instance

/-- *Náhodou* excludes the concord item at either verb position: the item needs inner
negation and the particle needs FALSUM (the paper's (17) and (18)). -/
theorem nahodou_excludes_nci (wp : VerbPosition) :
    ¬ ∃ pos ∈ wp.availableReadings, licenses pos .nciLicensed = true ∧
      NahodouLicensed .negative pos := by
  cases wp <;> decide

/-- *Náhodou* is felicitous with the polarity item at either verb position, the verb in situ
being licensed by FALSUM under a contrastive topic. -/
theorem nahodou_ppi (wp : VerbPosition) :
    ∃ pos ∈ wp.availableReadings, licenses pos .ppiOutscoping = true ∧
      NahodouLicensed .negative pos := by
  cases wp <;> decide

/-- *Náhodou* needs negation (the paper's (16)). -/
theorem nahodou_requires_negation (pos : Position) : ¬ NahodouLicensed .positive pos :=
  λ h => Polarity.noConfusion h.1

/-- The contextual evidence a *copak* question requires: evidence for the prejacent of a
positive question, against it for a negative one. -/
def Polarity.evidence : Polarity → ContextualEvidence
  | .positive => .forP
  | .negative => .againstP

/-- The speaker's prior belief a *copak* question conveys: against the prejacent of a
positive question, for it in a negative one (the paper's (19)). -/
def Polarity.prior : Polarity → OriginalBias
  | .positive => .againstP
  | .negative => .forP

/-- *Copak* is felicitous exactly when the context's evidence matches the question's
polarity. -/
def CopakLicensed (pol : Polarity) (ctx : ContextualEvidence) : Prop := ctx = pol.evidence

instance (pol : Polarity) (ctx : ContextualEvidence) : Decidable (CopakLicensed pol ctx) := by
  unfold CopakLicensed; infer_instance

/-- *Copak* is infelicitous without contextual evidence. -/
theorem copak_requires_bias (pol : Polarity) : ¬ CopakLicensed pol .neutral := by
  cases pol <;> decide

/-- *Copak* marks a conflict: the prior belief it conveys opposes the evidence it requires. -/
theorem copak_prior_ne_evidence (pol : Polarity) :
    (pol.prior = .forP ↔ pol.evidence = .againstP) ∧
      (pol.prior = .againstP ↔ pol.evidence = .forP) := by
  cases pol <;> decide

/-- The two particles part on context: *náhodou* is licensed by FALSUM whatever the
evidence, *copak* only under evidence. -/
theorem nahodou_copak_opposite (ctx : ContextualEvidence) :
    NahodouLicensed .negative .outer ∧ (CopakLicensed .negative ctx → ctx ≠ .neutral) := by
  cases ctx <;> decide

/-- Semantic classification of the Czech polar-question particles: the paper's two, and the
three of [stankova-2026]. -/
inductive ParticleSemantics
  /-- Modifies the ordering source of an epistemic modal (*náhodou*). -/
  | orderingSourceModifier
  /-- Temporal-endpoint presupposition (*ještě*). -/
  | temporalEndpoint
  /-- *Really*-type emphasis (*fakt*). -/
  | veridicalEmphasis
  /-- General negative polarity item (*vůbec*). -/
  | npi
  /-- Conflict between prior belief and contextual evidence (*copak*). -/
  | evidentialConflict
  deriving DecidableEq, Repr

/-- The paper's classification of its two particles. -/
def classification : List (Particle × ParticleSemantics) :=
  [(nahodou, .orderingSourceModifier), (copak, .evidentialConflict)]

end StankovaSimik2025
