import Linglib.Fragments.Slavic.Czech.Particles
import Linglib.Fragments.Slavic.Czech.PolarityItems
import Linglib.Semantics.Polarity.CzechNegation
import Linglib.Semantics.Questions.Bias
import Linglib.Logic.Modal.Defs
import Linglib.Studies.Simik2024

/-!
# Staňková and Šimík (2025): Negation in Czech Polar Questions

This file formalizes [stankova-2025]'s analysis of negation in Czech polar questions. The
negative prefix moves with the finite verb, so verb position fixes the position of negation:
a clause-initial verb sits above the canonical negation operator and can only be licensed by
the commitment operator FALSUM of [repp-2013] (`Simik2024.falsum`), while a verb in situ is licensed
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
(`falsum_broader_than_english_hiNQ`). The particle *náhodou* is licensed by FALSUM alone
(`Simik2024.NahodouLicensed`), so it excludes concord items whatever the word order
(`nahodou_excludes_nci`), and *copak* needs contextual evidence
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
open Czech.Negation
open Question
open Simik2024

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

/-- The lexical entry realizing each indefinite. -/
def Indefinite.entry : Indefinite → Polarity.Item
  | .nci => Czech.PolarityItems.zadny
  | .ppi => Czech.PolarityItems.nejaky

/-- The Table 1 diagnostic an indefinite tests, read off its entry's polarity class: a
positive polarity item tests whether the negation admits it, a concord item whether the
negation licenses it. -/
def Indefinite.diagnostic (ind : Indefinite) : Diagnostic :=
  if ind.entry.isPPI then .ppiOutscoping else .nciLicensed

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
  (∃ pos ∈ wp.availableReadings, pos.Licenses ind.diagnostic ∧ readingEvidenceOK pos ctx) ∧
    wordOrderEvidenceOK wp ctx

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

/-- *Náhodou* excludes the concord item at either verb position: the item needs inner
negation and the particle needs FALSUM (the paper's (17) and (18)). -/
theorem nahodou_excludes_nci (wp : VerbPosition) :
    ¬ ∃ pos ∈ wp.availableReadings, pos.Licenses .nciLicensed ∧ NahodouLicensed .negative pos := by
  cases wp <;> decide

/-- *Náhodou* is felicitous with the polarity item at either verb position, the verb in situ
being licensed by FALSUM under a contrastive topic. -/
theorem nahodou_ppi (wp : VerbPosition) :
    ∃ pos ∈ wp.availableReadings, pos.Licenses .ppiOutscoping ∧ NahodouLicensed .negative pos := by
  cases wp <;> decide

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
