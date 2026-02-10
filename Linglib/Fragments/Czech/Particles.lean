import Linglib.Phenomena.Negation.CzechThreeWayNeg

/-!
# Czech Diagnostic Particles

Particles and adverbs used as diagnostics for the three-way negation distinction
in Czech polar questions (Staňková 2026, Table 1).

## Key items

- *náhodou* 'by chance' — licensed only by outer negation (FALSUM)
- *ještě* 'yet/still' — licensed only by inner negation (propositional ¬)
- *fakt* 'really' — licensed by inner and medial, blocked by outer
- *vůbec* 'at all' — NPI, requires licensing by negation

These particles, together with the NCI/PPI determiner contrast
(`Fragments.Czech.Determiners`), form the five-column fingerprint
that uniquely identifies each negation position.

## Cross-linguistic connections

- *ještě* 'yet' parallels English *yet* (NPI, temporal endpoint)
- *fakt* 'really' relates to VERUM/FALSUM (Romero 2015, BiasedPQ.lean)
- *náhodou* 'by chance' modifies the ordering source of FALSUM's
  epistemic possibility component (Staňková §2.2.1)

## References

- Staňková, V. (2026). A three-way distinction of negation interpretation in Czech.
- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
  In B. Gehrke & R. Šimík (eds.), Topics in the semantics of Slavic languages.
-/

namespace Fragments.Czech.Particles

open Phenomena.Negation.CzechThreeWayNeg

-- ============================================================================
-- Particle Semantic Type
-- ============================================================================

/-- Semantic contribution type of the particle. -/
inductive ParticleSemantics where
  /-- Modifies the ordering source of an epistemic modal
      (widens to less stereotypical worlds). -/
  | orderingSourceModifier
  /-- Temporal endpoint: presupposes expected change of state.
      Requires propositional negation to create "not yet" meaning. -/
  | temporalEndpoint
  /-- Veridical emphasis: strengthens assertion/question commitment.
      Related to VERUM (Romero 2015). -/
  | veridicalEmphasis
  /-- General NPI: requires DE licensing. -/
  | npi
  /-- Indicates conflict between speaker's prior epistemic state and
      current contextual evidence. Requires evidential bias (biased context).
      Cross-Slavic: *copak* (Czech), *razve* (Russian), *zar* (Serbian). -/
  | evidentialConflict
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Particle Entry
-- ============================================================================

/-- A Czech particle entry with diagnostic properties. -/
structure ParticleEntry where
  /-- Surface form -/
  form : String
  /-- Gloss -/
  gloss : String
  /-- Semantic contribution -/
  semantics : ParticleSemantics
  /-- Which diagnostic from Staňková Table 1 this item corresponds to -/
  diagnostic : Option Diagnostic := none
  /-- Requires negation to be licensed (NPI-like behavior) -/
  requiresNeg : Bool := false
  /-- Brief description of licensing condition -/
  notes : String := ""
  deriving Repr, BEq

-- ============================================================================
-- The Czech Particle Lexicon
-- ============================================================================

/-- *náhodou* 'by chance, by any chance'

Only licensed by outer negation (FALSUM in PolP). *Náhodou* modifies the
ordering source of the epistemic possibility component in FALSUM, including
less stereotypical worlds in the modal base. This is why it's incompatible
with inner/medial negation: those don't involve FALSUM's modal component.

Staňková (2026 §2.2.1): "náhodou, which I translate as 'by any chance',
is only compatible with outer negation." -/
def nahodou : ParticleEntry :=
  { form := "náhodou"
  , gloss := "by.chance"
  , semantics := .orderingSourceModifier
  , diagnostic := some .nahodou
  , notes := "Modifies FALSUM ordering source; outer negation only" }

/-- *ještě* 'yet, still'

Only licensed by inner negation (propositional ¬ at TP). *Ještě* introduces
a temporal endpoint presupposition: the state described by p is expected to
eventually hold. Combined with inner negation, it yields "not yet p" = the
expected state hasn't been reached. This requires propositional negation,
which only inner negation provides.

Staňková (2026 §2.2.2): "ještě is only compatible with inner negation." -/
def jeste : ParticleEntry :=
  { form := "ještě"
  , gloss := "yet/still"
  , semantics := .temporalEndpoint
  , diagnostic := some .jeste
  , requiresNeg := true
  , notes := "Temporal endpoint presupposition; inner negation only" }

/-- *fakt* 'really'

Licensed by inner and medial negation, but blocked by outer negation.
*Fakt* functions as a veridical emphasis marker related to VERUM (Romero 2015).
It's incompatible with outer negation because outer negation is FALSUM —
combining VERUM emphasis with FALSUM creates a pragmatic contradiction.

Staňková (2026 §2.2.3): "fakt is compatible with inner and medial negation
but incompatible with outer negation." -/
def fakt : ParticleEntry :=
  { form := "fakt"
  , gloss := "really"
  , semantics := .veridicalEmphasis
  , diagnostic := some .fakt
  , notes := "VERUM-related; incompatible with FALSUM (outer neg)" }

/-- *vůbec* 'at all'

General NPI, requiring DE licensing. Licensed by inner negation (propositional ¬
is a DE context). Not one of the five Table 1 diagnostics, but an important
polarity item in Czech negated PQs.

Cross-linguistic parallel: English *at all* (`Fragments.English.PolarityItems.atAll`). -/
def vubec : ParticleEntry :=
  { form := "vůbec"
  , gloss := "at.all"
  , semantics := .npi
  , requiresNeg := true
  , notes := "General NPI; parallels English 'at all'" }

/-- *snad* 'perhaps, surely not'

Rhetorical/adversative particle in PQs and statements. Related to the
cross-Slavic family of PQ particles including Russian *razve*, Ukrainian
*xiba*, Belarusian *ci*, Polish *czyż(by)*, Bulgarian *nima*, and
Czech *copak/cožpak* (Šimík 2024 §4.2.4; Nekula 1996; Šebestová & Malá 2016;
Staňková 2023). Conveys surprise or doubt. -/
def snad : ParticleEntry :=
  { form := "snad"
  , gloss := "perhaps/surely.not"
  , semantics := .orderingSourceModifier
  , notes := "Adversative/mirative; cross-Slavic razve family" }

/-- *copak* 'what then, RAZVE'

Expresses a conflict between the speaker's prior belief and current
contextual evidence (Staňková & Šimík 2024 §6.2; Štícha 1995b, Nekula 1996,
Malá 2008, Šebestová & Malá 2016). Licensed in both positive and negative PQs,
but requires a biased context (evidential bias).

Key properties (Staňková & Šimík 2024 §6.2):
- Context-sensitive: requires biased context (z = 9.372, p < .001)
- In positive PQs: context implies ¬p, speaker believed p → surprise
- In negative PQs: context implies p, speaker believed ¬p → surprise
- Like word order and inner negation, copak is sensitive to contextual evidence

Contrast with *náhodou*: náhodou is FALSUM-tied (epistemic bias,
context-insensitive); copak is evidential-bias-tied (context-sensitive). -/
def copak : ParticleEntry :=
  { form := "copak"
  , gloss := "what.then/RAZVE"
  , semantics := .evidentialConflict
  , notes := "Requires evidential bias; cross-Slavic razve family" }

def allParticles : List ParticleEntry := [nahodou, jeste, fakt, vubec, snad, copak]

def lookup (form : String) : Option ParticleEntry :=
  allParticles.find? λ p => p.form == form

-- ============================================================================
-- Bridge to CzechThreeWayNeg: Negation Compatibility
-- ============================================================================

/-- Whether a particle is compatible with a given negation position,
derived from the `licenses` function in CzechThreeWayNeg. -/
def compatibleWith (p : ParticleEntry) (pos : NegPosition) : Bool :=
  match p.diagnostic with
  | some diag => licenses pos diag
  | none      => true  -- items without Table 1 diagnostics are unconstrained

-- Per-position compatibility for náhodou
theorem nahodou_inner  : compatibleWith nahodou .inner  = false := rfl
theorem nahodou_medial : compatibleWith nahodou .medial = false := rfl
theorem nahodou_outer  : compatibleWith nahodou .outer  = true  := rfl

-- Per-position compatibility for ještě
theorem jeste_inner  : compatibleWith jeste .inner  = true  := rfl
theorem jeste_medial : compatibleWith jeste .medial = false := rfl
theorem jeste_outer  : compatibleWith jeste .outer  = false := rfl

-- Per-position compatibility for fakt
theorem fakt_inner  : compatibleWith fakt .inner  = true  := rfl
theorem fakt_medial : compatibleWith fakt .medial = true  := rfl
theorem fakt_outer  : compatibleWith fakt .outer  = false := rfl

/-- *náhodou* uniquely identifies outer negation: it's the only particle
that is exclusively compatible with outer (and no other) position. -/
theorem nahodou_identifies_outer :
    ∀ pos : NegPosition,
      compatibleWith nahodou pos = true → pos = .outer := by
  intro pos; cases pos <;> decide

/-- *ještě* uniquely identifies inner negation: it's the only particle
that is exclusively compatible with inner (and no other) position. -/
theorem jeste_identifies_inner :
    ∀ pos : NegPosition,
      compatibleWith jeste pos = true → pos = .inner := by
  intro pos; cases pos <;> decide

/-- *fakt* distinguishes inner/medial from outer: it's compatible with
both inner and medial, but incompatible with outer. So if fakt is OK
but ještě is not, the reading must be medial. -/
theorem fakt_plus_no_jeste_identifies_medial :
    ∀ pos : NegPosition,
      (compatibleWith fakt pos = true ∧ compatibleWith jeste pos = false)
      → pos = .medial := by
  intro pos; cases pos <;> decide

/-- The three Table 1 particles {náhodou, ještě, fakt} together with the
NCI/PPI contrast suffice to uniquely identify each negation position.
Each position has a unique signature across the three particles. -/
theorem particle_signatures_distinct :
    (compatibleWith nahodou .inner, compatibleWith jeste .inner, compatibleWith fakt .inner) ≠
    (compatibleWith nahodou .medial, compatibleWith jeste .medial, compatibleWith fakt .medial) ∧
    (compatibleWith nahodou .inner, compatibleWith jeste .inner, compatibleWith fakt .inner) ≠
    (compatibleWith nahodou .outer, compatibleWith jeste .outer, compatibleWith fakt .outer) ∧
    (compatibleWith nahodou .medial, compatibleWith jeste .medial, compatibleWith fakt .medial) ≠
    (compatibleWith nahodou .outer, compatibleWith jeste .outer, compatibleWith fakt .outer) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- Context Sensitivity (Staňková & Šimík 2024 §6)
-- ============================================================================

/-! Corpus data (NahodouCorpusData, InterNPQUseCategory) and use category
distributions are in `Phenomena.Negation.CzechThreeWayNeg.Typology` §§20–21,
where they live alongside the other empirical data for these papers. -/

/-- Whether a particle requires evidential bias (biased context)
to be felicitous. Based on Staňková & Šimík (2024) §6:

- *náhodou*: no — FALSUM-tied, context-insensitive (§6.1)
- *copak*: yes — requires conflict between prior belief and evidence (§6.2)
- others: not experimentally tested for context sensitivity

Dispatches on `ParticleSemantics` and diagnostic status rather than surface
form. The `evidentialConflict` class inherently requires evidential bias.
For `orderingSourceModifier`, only experimentally tested particles (those
with a Table 1 diagnostic) get a definite classification. -/
def requiresEvidentialBias (p : ParticleEntry) : Option Bool :=
  match p.semantics with
  | .evidentialConflict     => some true   -- copak-class: requires biased context
  | .orderingSourceModifier =>
    match p.diagnostic with
    | some _ => some false  -- experimentally confirmed (náhodou): FALSUM-tied
    | none   => none        -- not experimentally tested (snad)
  | _                       => none        -- not experimentally tested

theorem nahodou_context_insensitive :
    requiresEvidentialBias nahodou = some false := rfl

theorem copak_context_sensitive :
    requiresEvidentialBias copak = some true := rfl

/-- náhodou and copak have opposite context requirements:
náhodou is tied to FALSUM (epistemic bias, context-insensitive),
while copak requires evidential bias (context-sensitive).
They express different bias dimensions (Staňková & Šimík 2024 §6). -/
theorem nahodou_copak_opposite_context :
    requiresEvidentialBias nahodou ≠ requiresEvidentialBias copak := by decide

/-- copak is not a Table 1 diagnostic (Staňková 2026) — it has no
direct negation-position licensing constraint. It appears in both
positive and negative PQs (Staňková & Šimík 2024 ex. 19a–b). -/
theorem copak_no_diagnostic : copak.diagnostic = none := rfl

/-- copak's semantics is evidentialConflict, distinct from
náhodou's orderingSourceModifier. -/
theorem copak_nahodou_different_semantics :
    copak.semantics ≠ nahodou.semantics := by decide

end Fragments.Czech.Particles
