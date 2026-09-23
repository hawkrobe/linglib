module

public import Linglib.Fragments.Slavic.Czech.Particles
public import Linglib.Fragments.Slavic.Czech.PolarityItems
public import Linglib.Logic.Modal.Defs
public import Linglib.Studies.Simik2024

/-!
# Staňková and Šimík (2025): Negation in Czech Polar Questions

This file formalizes [stankova-2025]'s analysis of negation in Czech polar questions. The
negative prefix moves with the finite verb, so verb position fixes the position of negation:
a clause-initial verb sits above the canonical negation operator and can only be licensed by
the commitment operator FALSUM of [repp-2013] (`Simik2024.falsum`), while a verb in situ is licensed
either by the operator or by FALSUM (`mem_availableReadings_iff`). The canonical operator
licenses negative concord items and is tied to negative contextual evidence; FALSUM allows
positive polarity items and conveys weak epistemic bias, indifferent to contextual evidence;
and declarative word order requires contextual evidence ([gunlogson-2002]). Which reading
licenses which indefinite is read off the lexical entries' polarity classes (`LicensedAt`),
so the two indefinites split the readings (`licensedAt_ppi_iff_not_nci`). Felicity of a
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

The readings of negation are [simik-2024]'s inner and outer negation. The main experiment (seventy-five speakers, a fully crossed design of verb position,
indefinite and context, cumulative link mixed models) found a main effect of the indefinite
in interrogative questions, no effect of context there, a preference for negative contexts
and for concord items in declarative questions, high naturalness of interrogative questions
under positive evidence, a main effect of the indefinite for *náhodou* questions, and a
main effect of context for *copak* questions; these results are stated in prose only.

## References

* [stankova-2025]
* [repp-2013]
* [zeijlstra-2004]
* [sudo-2013]
* [buring-gunlogson-2000]
* [nekula-1996]
* [simik-2024]
-/

@[expose] public section

namespace StankovaSimik2025

open Czech.Particles (nahodou copak)
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

/-- The readings of negation available at a verb position: the clause-initial verb raises
above the canonical operator and is licensed by FALSUM alone, the verb in situ by FALSUM or
by the canonical operator (the paper's (11) and (12)). -/
def VerbPosition.availableReadings : VerbPosition → List Negation
  | .v1 => [.outer]
  | .nonV1 => [.inner, .outer]

/-- A reading is available exactly when its operator c-commands the negated verb: FALSUM
always, the canonical operator only over the verb in situ. -/
theorem mem_availableReadings_iff (wp : VerbPosition) (n : Negation) :
    n ∈ wp.availableReadings ↔ n = .outer ∨ wp = .nonV1 := by
  cases wp <;> cases n <;> decide

/-- The unmarked reading at a verb position: the lowest available operator. -/
def VerbPosition.defaultReading : VerbPosition → Negation
  | .v1 => .outer
  | .nonV1 => .inner

theorem defaultReading_mem (wp : VerbPosition) : wp.defaultReading ∈ wp.availableReadings := by
  cases wp <;> decide

/-! ### Indefinites as proxies for the readings -/

/-- The indefinite manipulated in the experiment: the negative concord item *žádný*, a proxy
for inner negation, or the positive polarity item *nějaký*, a proxy for FALSUM. -/
inductive Indefinite
  | nci
  | ppi
  deriving DecidableEq, Repr, Fintype

/-- The lexical entry realizing each indefinite. -/
def Indefinite.entry : Indefinite → PolarityItem
  | .nci => Czech.PolarityItems.zadny
  | .ppi => Czech.PolarityItems.nejaky

/-- A polarity item is licensed at a reading of negation when a positive polarity item
falls under FALSUM and a negative one under the canonical operator (the paper's (11) and
(12)). -/
def LicensedAt (e : PolarityItem) (n : Negation) : Prop :=
  (e.isPPI → n = .outer) ∧ (e.isNPI → n = .inner)

instance (e : PolarityItem) (n : Negation) : Decidable (LicensedAt e n) := by
  unfold LicensedAt; infer_instance

/-- The two indefinites split the readings: the polarity item is licensed exactly where the
concord item is not. -/
theorem licensedAt_ppi_iff_not_nci (n : Negation) :
    LicensedAt Indefinite.ppi.entry n ↔ ¬ LicensedAt Indefinite.nci.entry n := by
  cases n <;> decide

/-! ### Bias and felicity -/

/-- The contextual evidence a reading of negation requires: the canonical operator
negative evidence, as in the evidentially biased contexts of [gunlogson-2002] and
[sudo-2013]; FALSUM, conveying epistemic rather than evidential bias, nothing. -/
def readingEvidenceOK : Negation → SignType → Prop
  | .inner, ctx => ctx = -1
  | .outer, _ => True

instance (n : Negation) (ctx : SignType) : Decidable (readingEvidenceOK n ctx) := by
  cases n <;> unfold readingEvidenceOK <;> infer_instance

/-- Declarative word order requires contextual evidence ([gunlogson-2002]); interrogative
word order requires none. -/
def wordOrderEvidenceOK : VerbPosition → SignType → Prop
  | .v1, _ => True
  | .nonV1, ctx => ctx ≠ 0

instance (wp : VerbPosition) (ctx : SignType) :
    Decidable (wordOrderEvidenceOK wp ctx) := by
  cases wp <;> unfold wordOrderEvidenceOK <;> infer_instance

/-- A negative polar question with an indefinite is felicitous in a context when some reading
available at its verb position licenses the indefinite and admits the context's evidence, and
the word order admits the evidence. -/
def Felicitous (wp : VerbPosition) (ind : Indefinite) (ctx : SignType) : Prop :=
  (∃ n ∈ wp.availableReadings, LicensedAt ind.entry n ∧ readingEvidenceOK n ctx) ∧
    wordOrderEvidenceOK wp ctx

instance (wp : VerbPosition) (ind : Indefinite) (ctx : SignType) :
    Decidable (Felicitous wp ind ctx) := by
  unfold Felicitous; infer_instance

/-- In interrogative questions the positive polarity item is felicitous in every context:
FALSUM licenses it and is indifferent to evidence. -/
theorem v1_ppi_any_context (ctx : SignType) : Felicitous .v1 .ppi ctx := by
  decide +revert

/-- In interrogative questions the negative concord item is never felicitous: the
clause-initial verb is out of reach of the canonical operator. -/
theorem v1_nci_never (ctx : SignType) : ¬ Felicitous .v1 .nci ctx := by
  decide +revert

/-- Interrogative questions are indifferent to the context. -/
theorem v1_context_invariant (ind : Indefinite) (ctx ctx' : SignType) :
    Felicitous .v1 ind ctx ↔ Felicitous .v1 ind ctx' := by
  decide +revert

/-- A declarative question with the concord item is felicitous exactly under negative
evidence: inner negation requires it. -/
theorem nonV1_nci_iff (ctx : SignType) :
    Felicitous .nonV1 .nci ctx ↔ ctx = -1 := by
  decide +revert

/-- A declarative question with the polarity item is felicitous exactly under some evidence:
FALSUM licenses the verb in situ, and the word order needs evidence. -/
theorem nonV1_ppi_iff (ctx : SignType) :
    Felicitous .nonV1 .ppi ctx ↔ ctx ≠ 0 := by
  decide +revert

/-- Declarative questions are infelicitous without contextual evidence. -/
theorem nonV1_neutral_infelicitous (ind : Indefinite) : ¬ Felicitous .nonV1 ind 0 := by
  cases ind <;> decide

/-- Czech FALSUM is broader than English high negation: an interrogative question with the
polarity item is felicitous under positive evidence (the paper's (14)), which the evidence
condition of [buring-gunlogson-2000] on English outer negation excludes. -/
theorem falsum_broader_than_english_hiNQ :
    ¬ BuringGunlogson2000.Felicitous .hiNQ 1 ∧
      Felicitous .v1 .ppi 1 :=
  ⟨by decide, v1_ppi_any_context _⟩

/-! ### The particles -/

/-- *Náhodou* excludes the concord item at either verb position: the item needs inner
negation and the particle needs FALSUM (the paper's (17) and (18)). -/
theorem nahodou_excludes_nci (wp : VerbPosition) :
    ¬ ∃ n ∈ wp.availableReadings,
      LicensedAt Indefinite.nci.entry n ∧ NahodouLicensed .negative n := by
  cases wp <;> decide

/-- *Náhodou* is felicitous with the polarity item at either verb position, the verb in situ
being licensed by FALSUM under a contrastive topic. -/
theorem nahodou_ppi (wp : VerbPosition) :
    ∃ n ∈ wp.availableReadings,
      LicensedAt Indefinite.ppi.entry n ∧ NahodouLicensed .negative n := by
  cases wp <;> decide

/-- *Copak* is felicitous exactly when the context's evidence matches the question's
polarity. -/
def CopakLicensed (pol : Polarity) (ctx : SignType) : Prop := ctx = evidence pol

instance (pol : Polarity) (ctx : SignType) : Decidable (CopakLicensed pol ctx) := by
  unfold CopakLicensed; infer_instance

/-- *Copak* is infelicitous without contextual evidence. -/
theorem copak_requires_bias (pol : Polarity) : ¬ CopakLicensed pol 0 := by
  cases pol <;> decide

/-- *Copak* marks a conflict: the prior belief it conveys opposes the evidence it requires. -/
theorem copak_prior_ne_evidence (pol : Polarity) :
    (prior pol = 1 ↔ evidence pol = -1) ∧
      (prior pol = -1 ↔ evidence pol = 1) := by
  cases pol <;> decide

/-- The two particles part on context: *náhodou* is licensed by FALSUM whatever the
evidence, *copak* only under evidence. -/
theorem nahodou_copak_opposite (ctx : SignType) :
    NahodouLicensed .negative .outer ∧ (CopakLicensed .negative ctx → ctx ≠ 0) := by
  decide +revert

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
