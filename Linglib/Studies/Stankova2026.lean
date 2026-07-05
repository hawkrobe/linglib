import Linglib.Semantics.Negation.CzechNegation
import Linglib.Studies.StankovaSimik2025

/-!
# Czech Three-Way Negation in Polar Questions
[stankova-2026] [stankova-2025] [zeijlstra-2004] [romero-2024]

Core empirical data for [stankova-2026], which proposes that negation in
Czech occupies three distinct LF positions in polar questions (her (16)):

| Position | LF site | Scope   | ne- > PPI | NCI | náhodou | ještě | fakt |
|----------|---------|---------|-----------|-----|---------|-------|------|
| inner    | TP      | narrow  | ✗         | ✓   | ✗       | ✓     | ✓    |
| medial   | ModP    | wide    | ✓         | ✗   | ✗       | ✗     | ✓    |
| outer    | PolP    | widest  | ✓         | ✗   | ✓       | ✗     | ✗    |

The three readings differ in (i) licensing conditions on polarity/concord items,
(ii) compatibility with particles *náhodou* 'by chance', *ještě* 'yet', *fakt*
'really', (iii) scope relative to the evidential bias modal □_ev, and (iv)
syntactic/prosodic encoding (word order and focus).

## Module Structure

This file contains per-cell verification theorems and scope generalizations.
The core types (`NegPosition`, `Diagnostic`, `licenses`) are in
`Semantics.Negation.CzechNegation`. Cross-linguistic bridges to
[romero-2024], [simik-2024], verb position, and bias profiles are in
`CzechThreeWayNeg.Typology`.

-/

namespace Stankova2026

open Semantics.Negation.CzechNegation

-- ============================================================================
-- §4: Per-Cell Verification Theorems
-- ============================================================================

/-! Each cell of Table 1 gets its own theorem. Changing any single entry in
`licenses` breaks exactly one theorem — maximum interconnection density. -/

-- Outer negation
theorem outer_licenses_ppi     : licenses .outer .ppiOutscoping = true  := rfl
theorem outer_blocks_nci       : licenses .outer .nciLicensed   = false := rfl
theorem outer_licenses_nahodou : licenses .outer .nahodou       = true  := rfl
theorem outer_blocks_jeste     : licenses .outer .jeste         = false := rfl
theorem outer_blocks_fakt      : licenses .outer .fakt          = false := rfl

-- Medial negation
theorem medial_licenses_ppi     : licenses .medial .ppiOutscoping = true  := rfl
theorem medial_blocks_nci       : licenses .medial .nciLicensed   = false := rfl
theorem medial_blocks_nahodou   : licenses .medial .nahodou       = false := rfl
theorem medial_blocks_jeste     : licenses .medial .jeste         = false := rfl
theorem medial_licenses_fakt    : licenses .medial .fakt          = true  := rfl

-- Inner negation
theorem inner_blocks_ppi       : licenses .inner .ppiOutscoping = false := rfl
theorem inner_licenses_nci     : licenses .inner .nciLicensed   = true  := rfl
theorem inner_blocks_nahodou   : licenses .inner .nahodou       = false := rfl
theorem inner_licenses_jeste   : licenses .inner .jeste         = true  := rfl
theorem inner_licenses_fakt    : licenses .inner .fakt          = true  := rfl

-- ============================================================================
-- §5: Uniqueness of Fingerprints
-- ============================================================================

/-- The Boolean signature of a negation position across all five diagnostics. -/
def signature (pos : NegPosition) : List Bool :=
  [ licenses pos .ppiOutscoping
  , licenses pos .nciLicensed
  , licenses pos .nahodou
  , licenses pos .jeste
  , licenses pos .fakt ]

/-- Each negation position has a unique diagnostic signature.
This is the empirical basis for the three-way distinction. -/
theorem signatures_distinct :
    signature .outer ≠ signature .medial ∧
    signature .outer ≠ signature .inner ∧
    signature .medial ≠ signature .inner := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold signature licenses; decide)

/-- The three positions exhaust all negation readings in Czech PQs. -/
theorem positions_exhaustive : ∀ p : NegPosition,
    p = .inner ∨ p = .medial ∨ p = .outer := by
  intro p; cases p <;> simp

-- ============================================================================
-- §6: Scope Generalizations
-- ============================================================================

/-- Only inner negation licenses NCIs — because only inner negation is in the
scope domain of the Agree relation. NCIs must be c-commanded
by ¬ at LF. Medial and outer negation are too high. -/
theorem only_inner_licenses_nci :
    (∀ p : NegPosition, licenses p .nciLicensed = true → p = .inner) := by
  intro p h; cases p <;> simp_all [licenses]

/-- Only outer negation licenses *náhodou* — because *náhodou* modifies the
ordering source of the epistemic possibility contributed by FALSUM,
including less stereotypical worlds (Staňková §2.2.1). -/
theorem only_outer_licenses_nahodou :
    (∀ p : NegPosition, licenses p .nahodou = true → p = .outer) := by
  intro p h; cases p <;> simp_all [licenses]

/-- Inner negation does not outscope PPIs — PPIs like *nějaký* must outscope
¬, but inner negation has narrow scope (within TP). So PPIs in the scope of
inner negation yield infelicity. -/
theorem inner_neg_cannot_outscope_ppi :
    licenses .inner .ppiOutscoping = false := rfl

/-- Both medial and outer license PPIs outscoping negation. -/
theorem noninner_licenses_ppi :
    licenses .medial .ppiOutscoping = true ∧
    licenses .outer .ppiOutscoping = true := ⟨rfl, rfl⟩

/-! ### The diagnostic particles ([stankova-2026] §2.2, Table 1)

*náhodou* and *copak* live with the experiments in
`StankovaSimik2025`; this paper contributes *ještě*, *fakt*, *vůbec*,
and *snad*, the Table 1 assignments, and the fingerprint results. -/

open StankovaSimik2025 (nahodou copak snad ParticleSemantics)

/-- *ještě* 'yet, still' — inner-negation diagnostic ([stankova-2026]
§2.2.2, (14)): with telic predicates it requires negation and in PQs is
felicitous only under inner negation (NCI or wide-scoping PPI), not
medial or outer; atelic *ještě* occurs without negation ((13a)). -/
def jeste : Particle where
  form := "ještě"
  distribution := some { polarInterrogative := some .optional }

/-- *fakt* 'really' — licensed by inner and medial negation, repelled by
outer on its canonical reading ([stankova-2026] §2.2.3, (15); the
'after all' reading is exempt, fn. 8). The paper defers its semantic
contribution, noting the parallels to English *really* (Romero & Han's
VERUM) and Russian *razve*. -/
def fakt : Particle where
  form := "fakt"
  distribution := some { polarInterrogative := some .optional }

/-- *vůbec* 'at all' — NPI, licensed by inner negation only among the
three readings ([stankova-2026] (9)-(10)); outside Table 1. Parallels
English *at all*. -/
def vubec : Particle where
  form := "vůbec"
  distribution := some { polarInterrogative := some .optional }

/-- The full six-particle inventory across the two papers. -/
def allParticles : List Particle :=
  [nahodou, jeste, fakt, vubec, snad, copak]

/-- This paper's classification of its four particles (the other two
are classified in `StankovaSimik2025.classification`). -/
def classification : List (Particle × ParticleSemantics) :=
  [(jeste, .temporalEndpoint), (fakt, .veridicalEmphasis),
   (vubec, .npi), (snad, .orderingSourceModifier)]

/-- [stankova-2026]'s Table 1: which diagnostic each particle
realizes. -/
def table1 : List (Particle × Diagnostic) :=
  [(nahodou, .nahodou), (jeste, .jeste), (fakt, .fakt)]

/-- The Table 1 diagnostic realized by `p`, if any. -/
def diagnostic? (p : Particle) : Option Diagnostic :=
  table1.lookup p

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

/-- *copak* is outside Table 1: it appears in positive and negative PQs
alike ([stankova-2025] exs. 19a-b). -/
theorem copak_no_diagnostic : diagnostic? copak = none := by decide

end Stankova2026
