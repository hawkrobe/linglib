import Linglib.Fragments.Slavic.Czech.Particles
import Linglib.Semantics.Polarity.CzechNegation

/-!
# Negation in Czech polar questions (Staňková & Šimík 2025)

This file formalizes [stankova-2025]: the main naturalness-rating
experiment on verb position and indefinite type in negative PQs (§5)
and the particle results — *náhodou* as an overt indicator of the
covert FALSUM operator (§6.1 subexperiment) and *copak* as sensitive
to contextual evidence (§6.2 subexperiment, exs. 19-20). The lexical
entries live in `Czech.Particles`; the three-way system and its
Table 1 diagnostics are [stankova-2026]'s and live in `Stankova2026`.

## Main results

* `VerbPosition.defaultReading`, `nci_diagnoses_nonV1`,
  `ppi_diagnoses_v1` — the main experiment's INDEFINITE effects derived
  from Table 1 licensing: PPIs preferred in V1 PQs, NCIs in nonV1.
* `requiresEvidentialBias`, `nahodou_copak_opposite_context` — the
  experimentally separated bias dimensions: *náhodou*
  context-insensitive, *copak* evidential-bias-sensitive.

## References

* [stankova-2025], [stankova-2023], [simik-2024], [nekula-1996].
-/

namespace StankovaSimik2025

open Czech.Particles (nahodou snad copak)
open Semantics.Negation.CzechNegation

/-! ### The main experiment (§5)

A 2×2×2 naturalness rating study (75 participants, Likert 1-7, CLMM
analysis) crossing verb position with indefinite type (NCI *žádný* vs
PPI *nějaký*) and context (negative vs neutral). The indefinites proxy
for the negation reading, so Table 1's licensing column derives the
observed directions: PPIs more natural in V1 PQs (p < .001), NCIs in
nonV1 (p < .001); context mattered only in nonV1 (p < .01, negative >
neutral) — FALSUM conveys epistemic, not evidential, bias. -/

/-- Verb position in Czech PQs: V1 (interrogative word order) vs nonV1
(declarative word order); *ne-* is inseparable from the finite verb, so
verb position fixes the syntactic position of negation (§2). -/
inductive VerbPosition where
  | v1
  | nonV1
  deriving DecidableEq, Repr

/-- Negation readings available per verb position ((11)-(12)): V1 only
outer; nonV1 also inner (outer there needs a contrastive topic and a
focused verb, ex. 18). The substrate's medial reading, [stankova-2026]'s
refinement, patterns with inner. -/
def VerbPosition.availableReadings : VerbPosition → List NegPosition
  | .v1    => [.outer]
  | .nonV1 => [.inner, .medial, .outer]

/-- The default (unmarked) negation reading per verb position. -/
def VerbPosition.defaultReading : VerbPosition → NegPosition
  | .v1    => .outer
  | .nonV1 => .inner

/-- Whether a verb position's default reading requires contextual
evidence (§5): V1 (FALSUM) is context-insensitive — natural under
positive, negative, and neutral evidential bias alike, unlike English
HiNQs — while nonV1 (inner) needs negative evidential bias. -/
def VerbPosition.requiresContextualEvidence : VerbPosition → Bool
  | .v1    => false
  | .nonV1 => true

/-- The default reading is always available. -/
theorem defaultReading_mem_availableReadings :
    ∀ wp : VerbPosition, wp.defaultReading ∈ wp.availableReadings := by
  intro wp; cases wp <;> decide

/-- An NCI-tolerant default reading diagnoses declarative word order:
the main experiment's NCI advantage in nonV1 PQs is inner negation. -/
theorem nci_diagnoses_nonV1 :
    ∀ wp : VerbPosition,
      licenses wp.defaultReading .nciLicensed = true → wp = .nonV1 := by
  intro wp; cases wp <;> decide

/-- Dually, a PPI-outscoping default diagnoses interrogative word order:
the PPI advantage in V1 PQs is outer negation (FALSUM). -/
theorem ppi_diagnoses_v1 :
    ∀ wp : VerbPosition,
      licenses wp.defaultReading .ppiOutscoping = true → wp = .v1 := by
  intro wp; cases wp <;> decide

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

/-- Whether a particle requires evidential bias: `some true` for
*copak* (§6.2), `some false` for the FALSUM-tied *náhodou* (§6.1,
acceptable in any type of context), `none` where untested. -/
def requiresEvidentialBias (p : Particle) : Option Bool :=
  if p = copak then some true
  else if p = nahodou then some false
  else none

/-- The §6.1 subexperiment: NCIs (inner negation) degrade *náhodou* PQs
(main effect of INDEFINITE, z = −12.845, p < .001), so *náhodou* "could
be used as an overt indicator of the covert FALSUM operator being
present in the structure" — and FALSUM is context-insensitive. -/
theorem nahodou_context_insensitive :
    requiresEvidentialBias nahodou = some false := by decide

/-- The §6.2 subexperiment: *copak* "strongly indicates a conflict
between speaker's prior belief and the currently available evidence"
(citing [nekula-1996]) — biased > neutral contexts, main effect of
CONTEXT, z = 9.372, p < .001; licensed in positive and negative PQs
alike (exs. 19a-b). Cross-Slavic kin: Polish *czyby*, Russian *razve*
(p. 12). -/
theorem copak_context_sensitive :
    requiresEvidentialBias copak = some true := by decide

/-- *náhodou* and *copak* express opposite bias dimensions: FALSUM-tied
and context-insensitive vs evidential-bias-tied and context-sensitive
([stankova-2025] §6, the two subexperiments). -/
theorem nahodou_copak_opposite_context :
    requiresEvidentialBias nahodou ≠ requiresEvidentialBias copak := by decide

end StankovaSimik2025
