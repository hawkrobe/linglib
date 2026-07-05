import Linglib.Fragments.Slavic.Czech.Particles
import Linglib.Semantics.Negation.CzechNegation

/-!
# Negation in Czech polar questions (Staňková & Šimík 2025)

This file formalizes [stankova-2025]'s particle results: *náhodou* as
an overt indicator of the covert FALSUM operator (§6.1 subexperiment)
and *copak* as sensitive to contextual evidence (§6.2 subexperiment,
exs. 19-20). The lexical entries live in `Czech.Particles`; the
three-way system and its Table 1 diagnostics are [stankova-2026]'s and
live in `Stankova2026`.

## Main results

* `requiresEvidentialBias`, `nahodou_copak_opposite_context` — the
  experimentally separated bias dimensions: *náhodou*
  context-insensitive, *copak* evidential-bias-sensitive.

## References

* [stankova-2025], [stankova-2023], [simik-2024], [nekula-1996].
-/

namespace StankovaSimik2025

open Czech.Particles (nahodou snad copak)

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
