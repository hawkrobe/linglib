import Linglib.Syntax.Particle.Capabilities
import Linglib.Semantics.Negation.CzechNegation

/-!
# Czech diagnostic particles (Staňková 2025)

This file formalizes [stankova-2025]'s particle diagnostics for the
three-way negation distinction in Czech polar questions: her Table 1
licensing profiles for *náhodou* / *ještě* / *fakt* prove that the
three negation positions of `Semantics.Negation.CzechNegation` are
uniquely identified by particle signatures, and her §6 experiments
separate the FALSUM-tied *náhodou* from the evidential-bias-tied
*copak*. Entries are `Particle` values (position cells `none` — the
paper records no placement data); the classifications are Staňková's
and live here as lookup tables, with Table 1 exposed as the
`Distributed Particle NegPosition` instance — the negation-position
licensing axis alongside the clause-type and embedding axes.

## Main results

* `nahodou_identifies_outer`, `jeste_identifies_inner`,
  `fakt_plus_no_jeste_identifies_medial` — each negation position is
  pinned by its Table 1 diagnostic.
* `particle_signatures_distinct` — the three diagnostics jointly
  fingerprint all three positions.
* `requiresEvidentialBias`, `nahodou_copak_opposite_context` — the §6
  bias dimensions: *náhodou* context-insensitive, *copak*
  evidential-bias-sensitive.
* `instance Distributed Particle NegPosition` — Table 1 as the third
  licensing axis.

## References

* [stankova-2025], [stankova-2023], [simik-2024], [romero-2019],
  [nekula-1996].
-/

namespace Stankova2025

open Semantics.Negation.CzechNegation

/-! ### The particles

All six occur in Czech polar questions, the paper's domain; other
clause-type cells and placements are unrecorded. -/

/-- *náhodou* 'by (any) chance' — "only compatible with outer negation"
([stankova-2025] §2.2.1): it modifies the ordering source of FALSUM's
epistemic possibility component, absent from inner/medial negation. -/
def nahodou : Particle where
  form := "náhodou"
  distribution := some { polarInterrogative := some .optional }

/-- *ještě* 'yet, still' — "only compatible with inner negation"
([stankova-2025] §2.2.2): its temporal-endpoint presupposition needs
the propositional negation that only inner negation provides. -/
def jeste : Particle where
  form := "ještě"
  distribution := some { polarInterrogative := some .optional }

/-- *fakt* 'really' — "compatible with inner and medial negation but
incompatible with outer negation" ([stankova-2025] §2.2.3): VERUM
emphasis clashes with FALSUM. -/
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

/-- *copak* 'what then' — conflict between prior belief and contextual
evidence ([stankova-2025] §6.2, [nekula-1996]): licensed in positive
and negative PQs alike, but requires a biased context; the Czech member
of the RAZVE family (*razve*, *nima*, *xiba*, *czyżby*, *zar*). -/
def copak : Particle where
  form := "copak"
  distribution := some { polarInterrogative := some .optional }

def allParticles : List Particle :=
  [nahodou, jeste, fakt, vubec, snad, copak]

/-! ### Staňková's classifications -/

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

/-- Staňková's classification, as a lookup table over the entries. -/
def classification : List (Particle × ParticleSemantics) :=
  [(nahodou, .orderingSourceModifier), (jeste, .temporalEndpoint),
   (fakt, .veridicalEmphasis), (vubec, .npi),
   (snad, .orderingSourceModifier), (copak, .evidentialConflict)]

/-- Staňková's classification of `p`, if any. -/
def semantics? (p : Particle) : Option ParticleSemantics :=
  classification.lookup p

/-- Table 1: which diagnostic each particle realizes. -/
def table1 : List (Particle × Diagnostic) :=
  [(nahodou, .nahodou), (jeste, .jeste), (fakt, .fakt)]

/-- The Table 1 diagnostic realized by `p`, if any. -/
def diagnostic? (p : Particle) : Option Diagnostic :=
  table1.lookup p

/-! ### Table 1 as the negation-position licensing axis

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

/-! ### The §6 bias dimensions -/

/-- Whether a particle requires evidential bias, per [stankova-2025]
§6: `some true` for the *copak* class, `some false` for the
experimentally confirmed FALSUM-tied *náhodou*, `none` where
untested. -/
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
([stankova-2025] §6). -/
theorem nahodou_copak_opposite_context :
    requiresEvidentialBias nahodou ≠ requiresEvidentialBias copak := by decide

/-- *copak* is outside Table 1: it appears in positive and negative PQs
alike ([stankova-2025] ex. 19a-b). -/
theorem copak_no_diagnostic : diagnostic? copak = none := by decide

end Stankova2025
