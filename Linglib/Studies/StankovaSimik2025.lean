import Linglib.Fragments.Slavic.Czech.Particles
import Linglib.Fragments.Slavic.Czech.Determiners
import Linglib.Semantics.Polarity.CzechNegation
import Linglib.Semantics.Questions.Bias
import Linglib.Data.Examples.StankovaSimik2025

/-!
# Negation in Czech polar questions (Staňková & Šimík 2025)

This file formalizes [stankova-2025], a naturalness-rating study of
negation in Czech polar questions. Verb position proxies the negation
reading — V1 forces FALSUM, nonV1 defaults to inner negation — with the
(11)-(12) reading inventory derived from c-command height and the §5.2
predictions derived from clash counting, checked against the typed
stimuli in `Data.Examples.StankovaSimik2025`. The subexperiments make
*náhodou* an overt FALSUM indicator (§6.1) and *copak* sensitive to
contextual evidence (§6.2). Lexical entries live in `Czech.Particles`
and `Czech.Determiners`; the three-way negation system and its Table 1
diagnostics are [stankova-2026]'s and live in `Stankova2026`.

## References

* [stankova-2025], [stankova-2023], [simik-2024], [nekula-1996].
-/

namespace StankovaSimik2025

open Czech.Particles (nahodou snad copak)
open Czech.Determiners (zadny nejaky)
open Czech.Negation
open Semantics.Questions.Bias (ContextualEvidence evidenceBiasOK)
open Features (Judgment)

/-! ### The main experiment (§5)

A 2×2×2 naturalness-rating design (75 participants, Likert 1-7, CLMM;
item (13)) crossing verb position, indefinite (NCI *žádný* vs PPI
*nějaký*), and context (negative vs neutral). PPIs are more natural in
V1 PQs (z = −15.674, p < .001) and NCIs in nonV1 (z = 6.208, p < 0.01);
context matters only in nonV1 (z = 8.674, p < 0.01; V1 n.s., z = −1.374,
p = 0.169; interaction z = 2.933, p < 0.01). In positive-evidence
contexts ((14), §5.3) V1 PQs stay natural (median 6, vs 5 neutral). -/

/-- Verb position in a Czech PQ — V1 (interrogative word order) or
nonV1 (declarative). Since *ne-* is inseparable from the finite verb,
verb position fixes the syntactic position of negation (§2). -/
inductive VerbPosition where
  | v1
  | nonV1
  deriving DecidableEq, Repr

/-- Height of the negated verb in `Position.toNat` coordinates; the
V1 verb raises into the outer (PolP) region, the nonV1 verb stays in TP
((11)-(12)). -/
def VerbPosition.verbHeight : VerbPosition → ℕ
  | .v1    => Position.outer.toNat
  | .nonV1 => Position.inner.toNat

/-- Negation readings available per verb position ((11)-(12)) — V1 only
outer; nonV1 also inner (outer there needs a contrastive topic and a
focused verb, ex. 18). The substrate's medial reading, [stankova-2026]'s
refinement, patterns with inner. -/
def VerbPosition.availableReadings : VerbPosition → List Position
  | .v1    => [.outer]
  | .nonV1 => [.inner, .medial, .outer]

/-- A reading is available at a verb position iff its operator sits at
or above the negated verb — the c-command condition behind (11)-(12). -/
theorem mem_availableReadings_iff (wp : VerbPosition) (pos : Position) :
    pos ∈ wp.availableReadings ↔ wp.verbHeight ≤ pos.toNat := by
  cases wp <;> cases pos <;> decide

/-- The default (unmarked) negation reading per verb position. -/
def VerbPosition.defaultReading : VerbPosition → Position
  | .v1    => .outer
  | .nonV1 => .inner

/-- The default reading is the narrowest-scope available one — canonical
inner negation wherever the verb position allows it. -/
theorem defaultReading_eq_min (wp : VerbPosition) :
    wp.availableReadings.min? = some wp.defaultReading := by
  cases wp <;> decide

/-- Whether a verb position's default reading requires contextual
evidence (§5). Context sensitivity tracks the reading, not the word
order; V1's FALSUM default is natural under any evidential bias,
nonV1's inner default needs negative evidence. -/
def VerbPosition.requiresContextualEvidence (wp : VerbPosition) : Bool :=
  wp.defaultReading.biasStrength == .strong

/-- An NCI-tolerant default reading identifies declarative word order;
the NCI advantage in nonV1 PQs diagnoses inner negation. -/
theorem nci_diagnoses_nonV1 :
    ∀ wp : VerbPosition,
      licenses wp.defaultReading .nciLicensed = true → wp = .nonV1 := by
  intro wp; cases wp <;> decide

/-- Dually, a PPI-outscoping default identifies interrogative word
order; the PPI advantage in V1 PQs diagnoses outer negation (FALSUM). -/
theorem ppi_diagnoses_v1 :
    ∀ wp : VerbPosition,
      licenses wp.defaultReading .ppiOutscoping = true → wp = .v1 := by
  intro wp; cases wp <;> decide

/-- The manipulated indefinite (§5.1), a proxy for the negation
reading — the NCI *žádný* for inner, the PPI *nějaký* for outer. -/
inductive Indefinite where
  | nci
  | ppi
  deriving DecidableEq, Repr

/-- The determiner entry realizing each indefinite. -/
def Indefinite.entry : Indefinite → Czech.Determiners.DetEntry
  | .nci => zadny
  | .ppi => nejaky

/-- The Table 1 diagnostic each indefinite tests. -/
def Indefinite.diagnostic : Indefinite → Diagnostic
  | .nci => .nciLicensed
  | .ppi => .ppiOutscoping

/-- The negation reading each indefinite proxies for (§5.1). -/
def Indefinite.reading : Indefinite → Position
  | .nci => .inner
  | .ppi => .outer

/-- Each indefinite tests exactly the diagnostic its determiner entry
carries. -/
theorem indefinite_diagnostic_matches_lexicon :
    ∀ ind : Indefinite, ind.entry.diagnostic = some ind.diagnostic := by
  intro ind; cases ind <;> rfl

/-! #### The §5.2 predictions

A condition is penalized once per clash — indefinite against default
reading, indefinite against context, verb position against context. -/

/-- The number of clashes in a condition of the §5.1 design. -/
def clashCount (wp : VerbPosition) (ind : Indefinite) (ctx : ContextualEvidence) : ℕ :=
  (if ind.reading == wp.defaultReading then 0 else 1) +
  (if (ind.reading.biasStrength == .strong) && (ctx != .againstP) then 1 else 0) +
  (if wp.requiresContextualEvidence && (ctx != .againstP) then 1 else 0)

/-- The judgment tier predicted from the clash count. -/
def predictedJudgment : ℕ → Judgment
  | 0 => .acceptable
  | 1 => .marginal
  | _ => .unacceptable

/-- In V1 PQs the PPI variant incurs fewer clashes than the NCI variant
in every context (the main effect of INDEFINITE). -/
theorem v1_ppi_preferred :
    ∀ ctx, clashCount .v1 .ppi ctx < clashCount .v1 .nci ctx := by
  intro ctx; cases ctx <;> decide

/-- V1 PQs with the matching PPI are equally natural in negative and
neutral contexts (the null effect of CONTEXT in V1). -/
theorem v1_ppi_context_invariant :
    clashCount .v1 .ppi .againstP = clashCount .v1 .ppi .neutral := rfl

/-- The INDEFINITE effect in V1 is larger in neutral contexts, where
the NCI also clashes with the context (the CONTEXT × INDEFINITE
interaction). -/
theorem v1_indefinite_context_interaction :
    clashCount .v1 .nci .againstP - clashCount .v1 .ppi .againstP <
    clashCount .v1 .nci .neutral - clashCount .v1 .ppi .neutral := by decide

/-- nonV1 PQs incur fewer clashes in negative than in neutral contexts
for either indefinite (the main effect of CONTEXT). -/
theorem nonV1_negative_context_preferred :
    ∀ ind, clashCount .nonV1 ind .againstP < clashCount .nonV1 ind .neutral := by
  intro ind; cases ind <;> decide

/-- In negative contexts the nonV1 NCI variant incurs fewer clashes
than the PPI variant (the main effect of INDEFINITE). -/
theorem nonV1_nci_preferred :
    clashCount .nonV1 .nci .againstP < clashCount .nonV1 .ppi .againstP := by decide

open Data.Examples (LinguisticExample)

/-- The (13) stimulus quadruple with each variant's verb position,
indefinite, and context. -/
def analyzedStimuli :
    List (LinguisticExample × VerbPosition × Indefinite × ContextualEvidence) :=
  [ (Examples.ex13_v1_nci,    .v1,    .nci, .neutral)
  , (Examples.ex13_v1_ppi,    .v1,    .ppi, .neutral)
  , (Examples.ex13_nonv1_nci, .nonV1, .nci, .againstP)
  , (Examples.ex13_nonv1_ppi, .nonV1, .ppi, .againstP) ]

/-- Each (13) variant is fully natural iff Table 1 licenses its
indefinite's diagnostic at the verb position's default reading. -/
theorem stimuli_match_default_licensing :
    analyzedStimuli.all (fun (e, wp, ind, _) =>
      (e.judgment == .acceptable) == licenses wp.defaultReading ind.diagnostic) = true := by
  decide

/-- Clash counting predicts each (13) variant's three-way judgment
tier. -/
theorem stimuli_match_clash_prediction :
    analyzedStimuli.all (fun (e, wp, ind, ctx) =>
      e.judgment == predictedJudgment (clashCount wp ind ctx)) = true := by
  decide

/-- The (14) stimulus is natural under positive evidence, the cell
[romero-2024]'s table rules out for English HiNQs (§5.3). -/
theorem falsum_broader_than_english_hiNQ :
    evidenceBiasOK .HiNQ .forP = false ∧ Examples.ex14.judgment = .acceptable :=
  ⟨rfl, rfl⟩

/-! ### Classification -/

/-- Semantic classification of the Czech PQ particles ([stankova-2025]
§6 for *náhodou*/*copak*; [stankova-2026] §2.2 supplies the rest via
`Stankova2026.classification`). -/
inductive ParticleSemantics where
  /-- Modifies the ordering source of an epistemic modal (*náhodou*;
      both papers' hypothesis). -/
  | orderingSourceModifier
  /-- Temporal-endpoint presupposition; with telic predicates needs
      propositional negation (*ještě*). -/
  | temporalEndpoint
  /-- 'Really'-type emphasis (*fakt*; semantics deferred by
      [stankova-2026], cf. VERUM). -/
  | veridicalEmphasis
  /-- General NPI (*vůbec*). -/
  | npi
  /-- Conflict between prior epistemic state and contextual evidence
      (*copak*; cross-Slavic RAZVE family). -/
  | evidentialConflict
  deriving DecidableEq, Repr

/-- This paper's classification of its two tested particles. -/
def classification : List (Particle × ParticleSemantics) :=
  [(nahodou, .orderingSourceModifier), (copak, .evidentialConflict)]

/-! ### The experimentally separated bias dimensions (§6) -/

/-- Whether a particle requires evidential bias — `some true` for
*copak* (§6.2), `some false` for the FALSUM-tied *náhodou* (§6.1,
acceptable in any type of context), `none` where untested. -/
def requiresEvidentialBias (p : Particle) : Option Bool :=
  if p = copak then some true
  else if p = nahodou then some false
  else none

/-- In the §6.1 subexperiment NCIs degrade *náhodou* PQs (z = −12.845,
p < .001), so *náhodou* "could be used as an overt indicator of the
covert FALSUM operator being present in the structure" — and FALSUM is
context-insensitive. -/
theorem nahodou_context_insensitive :
    requiresEvidentialBias nahodou = some false := by decide

/-- The §6.1 stimuli ((17) both variants, plus the nonV1 (18)) with the
diagnostic each manipulates. -/
def nahodouStimuli : List (LinguisticExample × Diagnostic) :=
  [ (Examples.ex17_ppi, .ppiOutscoping)
  , (Examples.ex17_nci, .nciLicensed)
  , (Examples.ex18,     .ppiOutscoping) ]

/-- *náhodou* pins the negation to FALSUM, so Table 1's outer row
predicts each §6.1 variant's naturalness regardless of verb position;
(18) is a nonV1 PQ and still patterns with outer negation. -/
theorem nahodou_stimuli_match_falsum :
    nahodouStimuli.all (fun (e, d) =>
      (e.judgment == .acceptable) == licenses .outer d) = true := by
  decide

/-- In the §6.2 subexperiment *copak* PQs are more natural in biased
than neutral contexts (z = 9.372, p < .001); *copak* "strongly
indicates a conflict between speaker's prior belief and the currently
available evidence" (citing [nekula-1996]), licensed in positive and
negative PQs alike (exs. 19a-b). Its cross-Slavic kin are Polish
*czyby* and Russian *razve* (p. 12). -/
theorem copak_context_sensitive :
    requiresEvidentialBias copak = some true := by decide

/-- *náhodou* and *copak* express opposite bias dimensions —
FALSUM-tied and context-insensitive vs evidential-bias-tied and
context-sensitive (§6, the two subexperiments). -/
theorem nahodou_copak_opposite_context :
    requiresEvidentialBias nahodou ≠ requiresEvidentialBias copak := by decide

end StankovaSimik2025
