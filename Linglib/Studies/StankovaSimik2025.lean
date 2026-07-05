import Linglib.Syntax.Particle.Capabilities
import Linglib.Semantics.Negation.CzechNegation

/-!
# Czech diagnostic particles (Staňková & Šimík 2025)

This file formalizes [stankova-2025]'s particle results for negation in
Czech polar questions — *náhodou* as an overt indicator of the covert
FALSUM operator (§6.1 subexperiment) and *copak* as sensitive to
contextual evidence (§6.2 subexperiment, exs. 19-20) — together with
the Table 1 particle diagnostics for the three-way negation system of
the companion work (`Stakov2026`), whose fingerprint theorems run over
`Semantics.Negation.CzechNegation`.

Source note: [stankova-2025] itself distinguishes two negation readings
(inner and outer); the three-way inner/medial/outer system and the
*ještě*/*fakt* diagnostics belong to the companion three-way analysis
and are flagged UNVERIFIED below pending that source.

## Main results

* `nahodou_identifies_outer`, `jeste_identifies_inner`,
  `fakt_plus_no_jeste_identifies_medial` — each negation position is
  pinned by its Table 1 diagnostic.
* `particle_signatures_distinct` — the three diagnostics jointly
  fingerprint all three positions.
* `requiresEvidentialBias`, `nahodou_copak_opposite_context` — the
  experimentally separated bias dimensions: *náhodou*
  context-insensitive, *copak* evidential-bias-sensitive.
* `instance Distributed Particle NegPosition` — the diagnostics as the
  third licensing axis.

## References

* [stankova-2025], [stankova-2023], [simik-2024], [romero-2019],
  [nekula-1996].
-/

namespace StankovaSimik2025

open Semantics.Negation.CzechNegation

/-! ### The particles

All six occur in Czech polar questions, the paper's domain; other
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

/-- *ještě* 'yet, still' — inner-negation diagnostic of the three-way
system (`Stakov2026`); its temporal-endpoint presupposition needs
propositional negation. -/
-- UNVERIFIED: not discussed in [stankova-2025]; source location in the
-- three-way companion pending.
def jeste : Particle where
  form := "ještě"
  distribution := some { polarInterrogative := some .optional }

/-- *fakt* 'really' — VERUM-related emphasis, compatible with inner and
medial negation but not outer (three-way system, `Stakov2026`). -/
-- UNVERIFIED: not discussed in [stankova-2025]; source location in the
-- three-way companion pending.
def fakt : Particle where
  form := "fakt"
  distribution := some { polarInterrogative := some .optional }

/-- *vůbec* 'at all' — general NPI, licensed by inner (propositional)
negation; outside Table 1. Parallels English *at all*. -/
def vubec : Particle where
  form := "vůbec"
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

def allParticles : List Particle :=
  [nahodou, jeste, fakt, vubec, snad, copak]

/-! ### The classifications -/

/-- Semantic classification of the diagnostic particles ([stankova-2025]
for *náhodou*/*copak*; the three-way companion for the rest). -/
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

/-- The classification, as a lookup table over the entries. -/
def classification : List (Particle × ParticleSemantics) :=
  [(nahodou, .orderingSourceModifier), (jeste, .temporalEndpoint),
   (fakt, .veridicalEmphasis), (vubec, .npi),
   (snad, .orderingSourceModifier), (copak, .evidentialConflict)]

/-- The classification of `p`, if any. -/
def semantics? (p : Particle) : Option ParticleSemantics :=
  classification.lookup p

/-- Table 1 of the three-way companion (`Stakov2026`): which diagnostic
each particle realizes. -/
-- UNVERIFIED: table attribution pending the three-way source.
def table1 : List (Particle × Diagnostic) :=
  [(nahodou, .nahodou), (jeste, .jeste), (fakt, .fakt)]

/-- The Table 1 diagnostic realized by `p`, if any. -/
def diagnostic? (p : Particle) : Option Diagnostic :=
  table1.lookup p

/-! ### The diagnostics as the negation-position licensing axis

Compatibility is read off the substrate's `licenses`; particles outside
Table 1 (*vůbec*, *snad*, *copak*) carry no recorded position
constraint. -/

/-- Table 1 as a `Distributed` axis: negation position is a licensing
context like clause type and embedding. -/
instance : Distributed Particle NegPosition :=
  ⟨fun p pos => (diagnostic? p).map fun d =>
    if licenses pos d then .optional else .excluded⟩

/-- Table 1 compatibility of a particle with a negation position, when
the particle carries a diagnostic. -/
def compatibleWith? (p : Particle) (pos : NegPosition) : Option Bool :=
  (diagnostic? p).map (licenses pos)

example : Distributed.LicensedIn nahodou NegPosition.outer := by decide

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

/-! ### The experimentally separated bias dimensions ([stankova-2025] §6) -/

/-- Whether a particle requires evidential bias: `some true` for the
*copak* class (§6.2), `some false` for the FALSUM-tied *náhodou*
(§6.1, acceptable in any type of context), `none` where untested. -/
def requiresEvidentialBias (p : Particle) : Option Bool :=
  match semantics? p with
  | some .evidentialConflict => some true
  | some .orderingSourceModifier => (diagnostic? p).map fun _ => false
  | _ => none

theorem nahodou_context_insensitive :
    requiresEvidentialBias nahodou = some false := by decide

theorem copak_context_sensitive :
    requiresEvidentialBias copak = some true := by decide

/-- *náhodou* and *copak* express opposite bias dimensions: FALSUM-tied
and context-insensitive vs evidential-bias-tied and context-sensitive
([stankova-2025] §6, the two subexperiments). -/
theorem nahodou_copak_opposite_context :
    requiresEvidentialBias nahodou ≠ requiresEvidentialBias copak := by decide

/-- *copak* is outside Table 1: it appears in positive and negative PQs
alike ([stankova-2025] exs. 19a-b). -/
theorem copak_no_diagnostic : diagnostic? copak = none := by decide

end StankovaSimik2025
