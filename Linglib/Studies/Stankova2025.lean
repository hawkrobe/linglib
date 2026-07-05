import Linglib.Semantics.Negation.CzechNegation

/-!
# Czech diagnostic particles (Staňková 2025)

This file formalizes [stankova-2025]'s particle diagnostics for the
three-way negation distinction in Czech polar questions: her Table 1
licensing profiles for *náhodou* / *ještě* / *fakt* prove that the
three negation positions of `Semantics.Negation.CzechNegation` are
uniquely identified by particle signatures, and her §6 experiments
separate the FALSUM-tied *náhodou* from the evidential-bias-tied
*copak*.

## Main results

* `nahodou_identifies_outer`, `jeste_identifies_inner`,
  `fakt_plus_no_jeste_identifies_medial` — each negation position is
  pinned by its Table 1 diagnostic.
* `particle_signatures_distinct` — the three diagnostics jointly
  fingerprint all three positions.
* `requiresEvidentialBias`, `nahodou_copak_opposite_context` — the §6
  bias dimensions: *náhodou* context-insensitive, *copak*
  evidential-bias-sensitive.

## References

* [stankova-2025], [stankova-2023], [simik-2024], [romero-2019],
  [nekula-1996].
-/

namespace Stankova2025

open Semantics.Negation.CzechNegation

/-- [stankova-2025]'s semantic classification of the diagnostic
particles. -/
inductive ParticleSemantics where
  /-- Modifies the ordering source of an epistemic modal (*náhodou*). -/
  | orderingSourceModifier
  /-- Temporal-endpoint presupposition; needs propositional negation
      (*ještě*). -/
  | temporalEndpoint
  /-- Veridical (VERUM-related) emphasis (*fakt*). -/
  | veridicalEmphasis
  /-- General NPI (*vůbec*). -/
  | npi
  /-- Conflict between prior epistemic state and contextual evidence
      (*copak*; cross-Slavic RAZVE family). -/
  | evidentialConflict
  deriving DecidableEq, Repr

/-- A Czech diagnostic-particle entry: form, [stankova-2025]
classification, Table 1 diagnostic if any, and NPI-hood. -/
structure ParticleEntry where
  /-- Surface form. -/
  form : String
  /-- [stankova-2025]'s semantic classification. -/
  semantics : ParticleSemantics
  /-- The Table 1 diagnostic this item realizes, if any. -/
  diagnostic : Option Diagnostic := none
  /-- Requires negation to be licensed. -/
  requiresNeg : Bool := false
  deriving DecidableEq, Repr

/-- *náhodou* 'by (any) chance' — "only compatible with outer negation"
([stankova-2025] §2.2.1): it modifies the ordering source of FALSUM's
epistemic possibility component, absent from inner/medial negation. -/
def nahodou : ParticleEntry :=
  { form := "náhodou", semantics := .orderingSourceModifier
    diagnostic := some .nahodou }

/-- *ještě* 'yet, still' — "only compatible with inner negation"
([stankova-2025] §2.2.2): its temporal-endpoint presupposition needs
the propositional negation that only inner negation provides. -/
def jeste : ParticleEntry :=
  { form := "ještě", semantics := .temporalEndpoint
    diagnostic := some .jeste, requiresNeg := true }

/-- *fakt* 'really' — "compatible with inner and medial negation but
incompatible with outer negation" ([stankova-2025] §2.2.3): VERUM
emphasis clashes with FALSUM. -/
def fakt : ParticleEntry :=
  { form := "fakt", semantics := .veridicalEmphasis
    diagnostic := some .fakt }

/-- *vůbec* 'at all' — general NPI, licensed by inner (propositional)
negation; outside Table 1. Parallels English *at all*. -/
def vubec : ParticleEntry :=
  { form := "vůbec", semantics := .npi, requiresNeg := true }

/-- *snad* 'perhaps, surely not' — adversative/mirative particle of the
cross-Slavic RAZVE family ([simik-2024] §4.2.4, [nekula-1996],
[stankova-2023]); not experimentally tested in [stankova-2025]. -/
def snad : ParticleEntry :=
  { form := "snad", semantics := .orderingSourceModifier }

/-- *copak* 'what then' — conflict between prior belief and contextual
evidence ([stankova-2025] §6.2, [nekula-1996]): licensed in positive
and negative PQs alike, but requires a biased context; the Czech member
of the RAZVE family. -/
def copak : ParticleEntry :=
  { form := "copak", semantics := .evidentialConflict }

def allParticles : List ParticleEntry :=
  [nahodou, jeste, fakt, vubec, snad, copak]

/-! ### Table 1: negation-position fingerprints

Compatibility is read off the substrate's `licenses`; particles outside
Table 1 (*vůbec*, *snad*, *copak*) carry no position constraint from
[stankova-2025] and are not assigned one here. -/

/-- Table 1 compatibility of a particle with a negation position, when
the particle carries a diagnostic. -/
def compatibleWith? (p : ParticleEntry) (pos : NegPosition) : Option Bool :=
  p.diagnostic.map (licenses pos)

/-- *náhodou* uniquely identifies outer negation. -/
theorem nahodou_identifies_outer :
    ∀ pos : NegPosition, compatibleWith? nahodou pos = some true → pos = .outer := by
  intro pos; cases pos <;> decide

/-- *ještě* uniquely identifies inner negation. -/
theorem jeste_identifies_inner :
    ∀ pos : NegPosition, compatibleWith? jeste pos = some true → pos = .inner := by
  intro pos; cases pos <;> decide

/-- *fakt* accepted while *ještě* is rejected identifies medial
negation. -/
theorem fakt_plus_no_jeste_identifies_medial :
    ∀ pos : NegPosition,
      compatibleWith? fakt pos = some true ∧ compatibleWith? jeste pos = some false →
      pos = .medial := by
  intro pos; cases pos <;> decide

/-- The three Table 1 diagnostics jointly fingerprint the three
negation positions: no two positions share a signature. -/
theorem particle_signatures_distinct :
    ∀ pos pos' : NegPosition,
      (∀ p ∈ [nahodou, jeste, fakt], compatibleWith? p pos = compatibleWith? p pos') →
      pos = pos' := by
  intro pos pos' h
  have h1 := h nahodou (by simp)
  have h2 := h jeste (by simp [jeste])
  have h3 := h fakt (by simp [fakt])
  revert h1 h2 h3
  cases pos <;> cases pos' <;> decide

/-! ### §6: bias dimensions -/

/-- Whether a particle requires evidential bias, per [stankova-2025]
§6: `some true` for the *copak* class, `some false` for the
experimentally confirmed FALSUM-tied *náhodou*, `none` where
untested. -/
def requiresEvidentialBias (p : ParticleEntry) : Option Bool :=
  match p.semantics with
  | .evidentialConflict => some true
  | .orderingSourceModifier => p.diagnostic.map fun _ => false
  | _ => none

theorem nahodou_context_insensitive :
    requiresEvidentialBias nahodou = some false := rfl

theorem copak_context_sensitive :
    requiresEvidentialBias copak = some true := rfl

/-- *náhodou* and *copak* express opposite bias dimensions: FALSUM-tied
and context-insensitive vs evidential-bias-tied and context-sensitive
([stankova-2025] §6). -/
theorem nahodou_copak_opposite_context :
    requiresEvidentialBias nahodou ≠ requiresEvidentialBias copak := by decide

/-- *copak* is outside Table 1: it appears in positive and negative PQs
alike ([stankova-2025] ex. 19a-b). -/
theorem copak_no_diagnostic : copak.diagnostic = none := rfl

end Stankova2025
