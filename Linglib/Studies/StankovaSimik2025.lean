import Linglib.Syntax.Particle.Capabilities
import Linglib.Semantics.Negation.CzechNegation

/-!
# Negation in Czech polar questions (Staňková & Šimík 2025)

This file formalizes [stankova-2025]'s particle results: *náhodou* as
an overt indicator of the covert FALSUM operator (§6.1 subexperiment)
and *copak* as sensitive to contextual evidence (§6.2 subexperiment,
exs. 19-20). The paper distinguishes two negation readings (inner and
outer); the three-way system and its Table 1 diagnostics are
[stankova-2026]'s and live in `Stankova2026`.

## Main results

* `requiresEvidentialBias`, `nahodou_copak_opposite_context` — the
  experimentally separated bias dimensions: *náhodou*
  context-insensitive, *copak* evidential-bias-sensitive.

## References

* [stankova-2025], [stankova-2023], [simik-2024], [nekula-1996].
-/

namespace StankovaSimik2025

/-! ### The particles

All occur in Czech polar questions, the paper's domain; other
clause-type cells and placements are unrecorded. -/

/-- *náhodou* 'by (any) chance' — licensed by FALSUM: the §6.1
subexperiment shows NCIs (inner negation) degrade *náhodou* PQs
(main effect of INDEFINITE, z = −12.845, p < .001), so *náhodou* "could
be used as an overt indicator of the covert FALSUM operator being
present in the structure" ([stankova-2025] §6.1). Insensitive to
contextual evidence, unlike *copak*. -/
def nahodou : Particle where
  form := "náhodou"
  distribution := some { polarInterrogative := some .optional }

/-- *snad* 'perhaps, surely not' — adversative/mirative particle of the
cross-Slavic RAZVE family ([simik-2024] §4.2.4, [nekula-1996],
[stankova-2023]); not experimentally tested in [stankova-2025]. -/
def snad : Particle where
  form := "snad"
  distribution := some { polarInterrogative := some .optional }

/-- *copak* 'what then' — "strongly indicates a conflict between
speaker's prior belief and the currently available evidence"
([stankova-2025] §6.2, citing [nekula-1996]): licensed in positive and
negative PQs alike (exs. 19a-b), requiring a context whose evidence
matches the PQ's polarity; the §6.2 subexperiment confirms the biased >
neutral preference (main effect of CONTEXT, z = 9.372, p < .001). The
Czech member of the cross-Slavic family with Polish *czyby* and Russian
*razve* (p. 12). -/
def copak : Particle where
  form := "copak"
  distribution := some { polarInterrogative := some .optional }

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

theorem nahodou_context_insensitive :
    requiresEvidentialBias nahodou = some false := by decide

theorem copak_context_sensitive :
    requiresEvidentialBias copak = some true := by decide

/-- *náhodou* and *copak* express opposite bias dimensions: FALSUM-tied
and context-insensitive vs evidential-bias-tied and context-sensitive
([stankova-2025] §6, the two subexperiments). -/
theorem nahodou_copak_opposite_context :
    requiresEvidentialBias nahodou ≠ requiresEvidentialBias copak := by decide

end StankovaSimik2025
