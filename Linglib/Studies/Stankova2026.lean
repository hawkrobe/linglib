import Linglib.Semantics.Negation.CzechNegation
import Linglib.Studies.StankovaSimik2025
import Linglib.Semantics.Questions.Bias.Defs

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

The core types (`NegPosition`, `Diagnostic`, `licenses`) are in
`Semantics.Negation.CzechNegation`; this file contains the per-cell
verification theorems, scope generalizations, the §2.2 diagnostic
particles, and the cross-linguistic typology bridges ([romero-2024],
[simik-2024], [gartner-gyuris-2017], verb position, bias profiles,
corpus data).
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

/-! ## Cross-linguistic typology

Bridges from the three-way distinction to [romero-2024]'s PQ typology,
[simik-2024]'s Czech PQ forms, and [gartner-gyuris-2017]'s bias
profiles, plus example and corpus data ([stankova-2025] for verb
position and context sensitivity). -/

-- ============================================================================
-- §7: NegPosition dot-notation extensions (must be in NegPosition's namespace)
-- ============================================================================

open Semantics.Questions.Bias

namespace Semantics.Negation.CzechNegation

/-- Map Czech negation positions to Romero's PQ form typology.

Czech VSO (interrogative) word order = high negation = HiNQ.
Czech SVO (declarative) word order = low negation = LoNQ.
Inner and medial are both syntactically low (SVO) but differ in LF scope.

Staňková (2026 §2): "When a PQ has the SVO word order, I call it declarative;
when a PQ has the VSO word order, I call it interrogative." -/
def NegPosition.toPQForm : NegPosition → PQForm
  | .inner  => .LoNQ  -- SVO, low negation
  | .medial => .LoNQ  -- SVO, low negation (ambiguous with inner)
  | .outer  => .HiNQ  -- VSO, high negation

/-- Map Czech negation positions to Romero's evidential bias strength.

Inner negation: strong contextual evidence bias (□_ev > ¬, must be ¬p).
Medial negation: weak contextual evidence bias (¬ > □_ev, needn't be p).
Outer negation: no contextual evidence bias (FALSUM, not □_ev-based). -/
def NegPosition.biasStrength : NegPosition → EvidentialBiasStrength
  | .inner  => .strong
  | .medial => .weak
  | .outer  => .none_

/-- Whether the negation position requires obligatory focus.

Only outer negation (FALSUM) is obligatorily focused — it targets discourse
polarity and generates alternatives on whether p is or isn't in the CommonGround
(Staňková §3.2, §4). -/
def NegPosition.requiresFocus : NegPosition → Bool
  | .outer  => true
  | .medial => false
  | .inner  => false

end Semantics.Negation.CzechNegation

namespace Stankova2026

open Semantics.Negation.CzechNegation
open Semantics.Questions.Bias

/-- Outer negation maps to HiNQ (high negation = interrogative word order). -/
theorem outer_is_hiNQ : NegPosition.outer.toPQForm = .HiNQ := rfl

/-- Inner and medial both map to LoNQ (low negation = declarative word order).
Czech low negation PQs are ambiguous between inner and medial readings,
distinguished by polarity items and particles (Table 1). -/
theorem inner_medial_are_loNQ :
    NegPosition.inner.toPQForm = .LoNQ ∧
    NegPosition.medial.toPQForm = .LoNQ := ⟨rfl, rfl⟩

theorem inner_strong_bias : NegPosition.inner.biasStrength = .strong := rfl
theorem medial_weak_bias : NegPosition.medial.biasStrength = .weak := rfl
theorem outer_no_bias : NegPosition.outer.biasStrength = .none_ := rfl

/-- Czech outer negation (HiNQ) requires original speaker bias for p,
matching Romero's Table 1: HiNQs mandatorily convey bias for p. -/
theorem czech_outer_matches_romero_hiNQ_bias :
    NegPosition.outer.toPQForm = .HiNQ ∧
    originalBiasOK .HiNQ .forP = true ∧
    originalBiasOK .HiNQ .neutral = false := ⟨rfl, rfl, rfl⟩

/-- Czech inner/medial negation (LoNQ) is compatible with neutral original bias,
matching Romero's Table 1: LoNQs can be used without prior expectation. -/
theorem czech_low_neg_matches_romero_loNQ_bias :
    NegPosition.inner.toPQForm = .LoNQ ∧
    originalBiasOK .LoNQ .neutral = true := ⟨rfl, rfl⟩

/-- Czech inner negation requires contextual evidence against p (Staňková §3.1,
ex. 17a/18a). This matches Romero's Table 2: LoNQs require evidence against p. -/
theorem czech_inner_matches_romero_evidence_bias :
    NegPosition.inner.toPQForm = .LoNQ ∧
    evidenceBiasOK .LoNQ .againstP = true := ⟨rfl, rfl⟩

/-- Czech outer negation (HiNQ) is compatible with evidence against p
(contradiction scenarios, Staňková ex. 24 / Romero ex. 15). -/
theorem czech_outer_matches_romero_evidence :
    NegPosition.outer.toPQForm = .HiNQ ∧
    evidenceBiasOK .HiNQ .againstP = true := ⟨rfl, rfl⟩

-- ============================================================================
-- §8: Bridge to Focus / Information Structure
-- ============================================================================

theorem only_outer_requires_focus :
    (∀ p : NegPosition, p.requiresFocus = true → p = .outer) := by
  intro p h; cases p <;> simp_all [NegPosition.requiresFocus]

-- ============================================================================
-- §9: Example Data
-- ============================================================================

/-- Verb position in Czech polar questions ([stankova-2025] §2).

Czech PQs use two word orders, determined by whether the finite verb
moves to clause-initial position:
- **V1** (verb-initial): interrogative word order, verb+ne- in PolP
- **nonV1** (non-verb-initial): declarative word order, verb+ne- in TP

Since Czech negation prefix *ne-* is inseparable from the verb,
verb position directly determines the syntactic position of negation.
This creates the surface syntax–negation interpretation mapping
([zeijlstra-2004] Agree analysis, S&Š eqs. 11–12). -/
inductive VerbPosition where
  /-- Verb-initial (interrogative) word order.
      The verb+ne- moves to PolP, within the scope of FALSUM[iNeg].
      Only outer negation (FALSUM) is available (S&Š eq. 11). -/
  | v1
  /-- Non-verb-initial (declarative) word order.
      The verb+ne- stays low in TP. Can be licensed by either
      FALSUM[iNeg] or Op¬[iNeg], but not both simultaneously (S&Š eq. 12). -/
  | nonV1
  deriving DecidableEq, Repr

end Stankova2026

namespace Semantics.Negation.CzechNegation
open Stankova2026 (VerbPosition)

/-- Map negation positions to verb position.

Inner/medial → nonV1 (declarative SVO).
Outer → v1 (interrogative VSO). -/
def NegPosition.toVerbPosition : NegPosition → VerbPosition
  | .inner  => .nonV1
  | .medial => .nonV1
  | .outer  => .v1

end Semantics.Negation.CzechNegation

namespace Stankova2026
open Semantics.Negation.CzechNegation
open Semantics.Questions.Bias
open Stankova2026 (signature)

/-- A Czech PQ negation example with its reading and Romero classification. -/
structure CzechNegDatum where
  /-- The Czech sentence -/
  sentence : String
  /-- Glossed translation -/
  gloss : String
  /-- English translation -/
  english : String
  /-- The negation reading (Staňková 2026) -/
  position : NegPosition
  /-- Whether the example is grammatical -/
  grammatical : Bool
  /-- Reference example number from Staňková 2026 -/
  exampleNum : String
  /-- Verb position derived from negation position -/
  verbPosition : VerbPosition := position.toVerbPosition
  /-- Romero PQ form derived from negation position -/
  pqForm : PQForm := position.toPQForm
  deriving Repr

/-- Ex. (6a): Inner negation with NCI — grammatical. -/
def ex6a : CzechNegDatum :=
  { sentence := "Petr si nekoupil žádný časopis?"
  , gloss := "Petr REFL NEG.bought DET.NCI magazine"
  , english := "Petr didn't buy any magazine?"
  , position := .inner
  , grammatical := true
  , exampleNum := "6a" }

/-- Ex. (6b): Outer negation with NCI — ungrammatical. -/
def ex6b : CzechNegDatum :=
  { sentence := "*Nekoupil si Petr žádný časopis?"
  , gloss := "NEG.bought REFL Petr DET.NCI magazine"
  , english := "Didn't Petr buy a magazine?"
  , position := .outer
  , grammatical := false
  , exampleNum := "6b" }

/-- Ex. (7a): Medial negation with PPI — grammatical. -/
def ex7a : CzechNegDatum :=
  { sentence := "Eva si neobjednala nějaký burger?"
  , gloss := "Eva REFL NEG.ordered DET.PPI burger"
  , english := "Eva didn't order some burger?"
  , position := .medial
  , grammatical := true
  , exampleNum := "7a" }

/-- Ex. (7b): Outer negation with PPI — grammatical. -/
def ex7b : CzechNegDatum :=
  { sentence := "Neobjednala si Eva nějaký burger?"
  , gloss := "NEG.ordered REFL Eva DET.PPI burger"
  , english := "Didn't Eva order some burger?"
  , position := .outer
  , grammatical := true
  , exampleNum := "7b" }

/-- Ex. (11): Outer negation with *náhodou* — grammatical. -/
def ex11 : CzechNegDatum :=
  { sentence := "Nepůjčila si tam Eva náhodou nějakou encyklopedii?"
  , gloss := "NEG.borrowed REFL there Eva NÁHODOU DET.PPI encyclopedia"
  , english := "Didn't Eva borrow some encyclopedia, by any chance?"
  , position := .outer
  , grammatical := true
  , exampleNum := "11" }

/-- Ex. (15a): Inner negation with *fakt* — grammatical. -/
def ex15a : CzechNegDatum :=
  { sentence := "Eva fakt neviděla žádný Tarantinův film?"
  , gloss := "Eva FAKT NEG.saw DET.NCI Tarantino's film"
  , english := "Eva really hasn't seen any film by Tarantino?"
  , position := .inner
  , grammatical := true
  , exampleNum := "15a" }

/-- Ex. (15d): Outer negation with *fakt* — ungrammatical. -/
def ex15d : CzechNegDatum :=
  { sentence := "*Neviděla Eva fakt nějaký Tarantinův film?"
  , gloss := "NEG.saw Eva FAKT DET.PPI Tarantino's film"
  , english := "Is it really not the case that Eva has seen a film by Tarantino?"
  , position := .outer
  , grammatical := false
  , exampleNum := "15d" }

def allExamples : List CzechNegDatum :=
  [ex6a, ex6b, ex7a, ex7b, ex11, ex15a, ex15d]

-- ============================================================================
-- §10: Per-Example Verification
-- ============================================================================

/-- Examples predicted grammatical by Table 1 are marked grammatical. -/
theorem ex6a_grammatical_iff_inner_licenses_nci :
    ex6a.grammatical = licenses ex6a.position .nciLicensed := rfl

theorem ex6b_ungrammatical_iff_outer_blocks_nci :
    ex6b.grammatical = licenses ex6b.position .nciLicensed := rfl

theorem ex7a_grammatical_iff_medial_licenses_ppi :
    ex7a.grammatical = licenses ex7a.position .ppiOutscoping := rfl

theorem ex7b_grammatical_iff_outer_licenses_ppi :
    ex7b.grammatical = licenses ex7b.position .ppiOutscoping := rfl

theorem ex11_grammatical_iff_outer_licenses_nahodou :
    ex11.grammatical = licenses ex11.position .nahodou := rfl

theorem ex15a_grammatical_iff_inner_licenses_fakt :
    ex15a.grammatical = licenses ex15a.position .fakt := rfl

theorem ex15d_ungrammatical_iff_outer_blocks_fakt :
    ex15d.grammatical = licenses ex15d.position .fakt := rfl

-- ============================================================================
-- §11: Per-Example Romero Classification
-- ============================================================================

/-! Each Czech example carries its Romero PQ form automatically via
`NegPosition.toPQForm`. These bridge theorems verify that the classification
is consistent with the word order and bias conditions. -/

/-- Ex. 6a (inner, nonV1) is a LoNQ. -/
theorem ex6a_is_loNQ : ex6a.pqForm = .LoNQ := rfl

/-- Ex. 6b (outer, V1) is a HiNQ. -/
theorem ex6b_is_hiNQ : ex6b.pqForm = .HiNQ := rfl

/-- Ex. 7a (medial, nonV1) is a LoNQ. -/
theorem ex7a_is_loNQ : ex7a.pqForm = .LoNQ := rfl

/-- Ex. 7b (outer, V1) is a HiNQ. -/
theorem ex7b_is_hiNQ : ex7b.pqForm = .HiNQ := rfl

/-- Ex. 11 (outer, V1) is a HiNQ with *náhodou*. -/
theorem ex11_is_hiNQ : ex11.pqForm = .HiNQ := rfl

/-- Ex. 15a (inner, nonV1) is a LoNQ with *fakt*. -/
theorem ex15a_is_loNQ : ex15a.pqForm = .LoNQ := rfl

/-- Ex. 15d (outer, V1) is a HiNQ — *fakt* is incompatible. -/
theorem ex15d_is_hiNQ : ex15d.pqForm = .HiNQ := rfl

-- ============================================================================
-- §12: Romero Bias Predictions for Czech Examples
-- ============================================================================

/-! Romero's Tables 1–2 make predictions about which Czech examples should be
felicitous. These bridge theorems verify that Staňková's Czech data is
consistent with Romero's cross-linguistic generalizations. -/

/-- Ex. 6b is a HiNQ. Romero Table 1 says HiNQ mandatorily conveys original
bias for p. The example IS a HiNQ but is ungrammatical because the NCI *žádný*
is incompatible with outer negation — a Czech-specific constraint layered on
top of the Romero framework. -/
theorem ex6b_hiNQ_blocked_by_nci :
    ex6b.pqForm = .HiNQ ∧
    originalBiasOK ex6b.pqForm .forP = true ∧
    licenses ex6b.position .nciLicensed = false := ⟨rfl, rfl, rfl⟩

/-- Ex. 7b is a HiNQ (outer, V1) with a PPI. Romero Table 1: HiNQ requires
original bias for p. The PPI is licensed because outer negation allows PPI
outscoping. This is a felicitous Czech HiNQ consistent with Romero. -/
theorem ex7b_hiNQ_consistent_with_romero :
    ex7b.pqForm = .HiNQ ∧
    ex7b.grammatical = true ∧
    originalBiasOK ex7b.pqForm .forP = true ∧
    licenses ex7b.position .ppiOutscoping = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Ex. 11 is a HiNQ with *náhodou* 'by chance'. This is the prototypical
outer-HiNQ: original speaker bias for p (Romero Table 1), compatible with
neutral or against-p evidence (Romero Table 2). *Náhodou* modifies the
epistemic possibility component of FALSUM. -/
theorem ex11_hiNQ_with_nahodou :
    ex11.pqForm = .HiNQ ∧
    ex11.grammatical = true ∧
    originalBiasOK ex11.pqForm .forP = true ∧
    evidenceBiasOK ex11.pqForm .neutral = true ∧
    licenses ex11.position .nahodou = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Ex. 7a (medial, nonV1, LoNQ) is felicitous in contexts with some evidence
against p. Romero Table 2: LoNQ requires evidence against p. Staňková's
medial negation carries weak evidential bias — weaker than inner, but still
requires contextual evidence. -/
theorem ex7a_loNQ_with_evidence :
    ex7a.pqForm = .LoNQ ∧
    ex7a.grammatical = true ∧
    evidenceBiasOK ex7a.pqForm .againstP = true ∧
    ex7a.position.biasStrength = .weak := ⟨rfl, rfl, rfl, rfl⟩

/-- Ex. 6a (inner, nonV1, LoNQ) is felicitous only with strong contextual
evidence against p. Romero Table 2: LoNQ requires evidence against p.
Staňková adds the refinement that inner neg requires *strong* evidence
(the inner/medial split within LoNQ). -/
theorem ex6a_loNQ_strong_evidence :
    ex6a.pqForm = .LoNQ ∧
    ex6a.grammatical = true ∧
    evidenceBiasOK ex6a.pqForm .againstP = true ∧
    ex6a.position.biasStrength = .strong := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §13: Czech Refines Romero's LoNQ
-- ============================================================================

/-- Czech reveals a finer-grained distinction within Romero's LoNQ category.

Romero treats LoNQ as a single PQ form. Staňková shows that Czech SVO
(= LoNQ) polar questions are actually ambiguous between inner and medial
readings, distinguished by their diagnostic signatures (Table 1) and by
the strength of their evidential bias.

This is a cross-linguistic prediction: languages with overt NCI/PPI contrasts
and diagnostic particles may reveal the inner/medial split within LoNQ. -/
theorem czech_refines_loNQ :
    NegPosition.inner.toPQForm = NegPosition.medial.toPQForm ∧   -- both LoNQ
    NegPosition.inner.biasStrength ≠ NegPosition.medial.biasStrength ∧  -- different bias
    signature .inner ≠ signature .medial :=                      -- different diagnostics
  ⟨rfl, by decide, by (unfold signature licenses; decide)⟩

-- ============================================================================
-- §14: Czech PQ Form Typology ([simik-2024] §3.2)
-- ============================================================================

/-- Czech polar question forms: the 2×2 grid of [Interrogative vs Declarative]
× [Positive vs Negative] ([simik-2024] §3.2, exx. 11–17).

Czech uses two independent formal strategies to express bias:
1. **Negation**: positive vs negative (ne- prefix)
2. **Word order**: interrogative (VSO, verb-initial) vs declarative (SVO)

This is finer-grained than Romero's PosQ/LoNQ/HiNQ, because Czech
declarative PQs (DeclPQ) are a separate grammatical category not present
in English ([simik-2024]: "declarative PQs represent yet another type of utterance
with a canonical SVO word order"). -/
inductive CzechPQForm where
  /-- InterPPQ: Interrogative (VSO), Positive. Default unbiased PQ. -/
  | interPPQ
  /-- InterNPQ: Interrogative (VSO), Negative. Conveys positive epistemic bias.
      Broader distribution than English HiNQ ([simik-2024] §5). -/
  | interNPQ
  /-- DeclPPQ: Declarative (SVO), Positive. Conveys positive evidential bias. -/
  | declPPQ
  /-- DeclNPQ: Declarative (SVO), Negative. Requires negative evidential bias. -/
  | declNPQ
  deriving DecidableEq, Repr

/-- Map Czech PQ forms to Romero's cross-linguistic PQ typology.

[simik-2024]'s InterNPQ is Romero's HiNQ (outer negation with VSO).
[simik-2024]'s DeclNPQ is Romero's LoNQ (inner/medial negation with SVO).
[simik-2024]'s InterPPQ and DeclPPQ are both Romero's PosQ. -/
def CzechPQForm.toPQForm : CzechPQForm → PQForm
  | .interPPQ => .PosQ
  | .interNPQ => .HiNQ  -- outer negation, verb-initial
  | .declPPQ  => .PosQ
  | .declNPQ  => .LoNQ  -- inner/medial negation, declarative

theorem interNPQ_is_hiNQ : CzechPQForm.interNPQ.toPQForm = .HiNQ := rfl
theorem declNPQ_is_loNQ : CzechPQForm.declNPQ.toPQForm = .LoNQ := rfl

end Stankova2026

namespace Semantics.Negation.CzechNegation
open Stankova2026 (CzechPQForm)

/-- Map negation positions to Czech PQ forms.

Inner/medial → DeclNPQ (SVO, negative).
Outer → InterNPQ (VSO, negative). -/
def NegPosition.toCzechPQForm : NegPosition → CzechPQForm
  | .inner  => .declNPQ
  | .medial => .declNPQ
  | .outer  => .interNPQ

end Semantics.Negation.CzechNegation

namespace Stankova2026
open Semantics.Negation.CzechNegation
open Semantics.Questions.Bias

/-- The CzechPQForm → PQForm mapping is consistent with NegPosition → PQForm. -/
theorem czechPQForm_consistent_with_pqForm :
    ∀ pos : NegPosition,
      pos.toCzechPQForm.toPQForm = pos.toPQForm := by
  intro pos; cases pos <;> rfl

-- ============================================================================
-- §15: Czech Bias Profiles ([simik-2024], Table 2 / [stankova-2023])
-- ============================================================================

/-- Czech bias profile ([simik-2024] Table 2, based on [stankova-2023]).

Each cell records which Czech PQ forms are felicitous under a given
combination of contextual evidence × original speaker bias. Empty list = no
form is natural.

Uses `ContextualEvidence` and `OriginalBias` from Bias
rather than Czech-specific copies — these are the same bias dimensions.

Table 2 (glossing over details):
| Evid \ Epist | forP               | neutral            | againstP   |
|--------------|--------------------|--------------------|------------|
| forP         |                    | DeclPPQ, InterNPQ  | DeclPPQ    |
| neutral      | InterPPQ, InterNPQ | InterPPQ           |            |
| againstP     | DeclNPQ, InterNPQ  | DeclNPQ            |            |

*DeclPPQ with neutral/neutral is conditioned by information structure.
InterNPQ with neutral epistemic requires explanation-seeking context. -/
def czechBiasProfile : ContextualEvidence → OriginalBias → List CzechPQForm
  | .forP,     .forP     => []  -- no form natural in this cell
  | .forP,     .neutral   => [.declPPQ, .interNPQ]
  | .forP,     .againstP  => [.declPPQ]
  | .neutral,  .forP      => [.interPPQ, .interNPQ]
  | .neutral,  .neutral   => [.interPPQ]  -- default: InterPPQ
  | .neutral,  .againstP  => []
  | .againstP, .forP      => [.declNPQ, .interNPQ]
  | .againstP, .neutral   => [.declNPQ]
  | .againstP, .againstP  => []

/-- InterPPQ is the default (unbiased) Czech PQ — the only form felicitous
in quiz scenarios where no bias is intended ([simik-2024] §4.1, ex. 25). -/
theorem interPPQ_is_default :
    (czechBiasProfile .neutral .neutral).contains .interPPQ = true := rfl

/-- DeclPQs require matching evidential bias ([stankova-2023], [simik-2024] §3.2):
DeclPPQ needs positive evidence, DeclNPQ needs negative evidence. -/
theorem declPPQ_requires_positive_evidence :
    (czechBiasProfile .forP .neutral).contains .declPPQ = true ∧
    (czechBiasProfile .againstP .neutral).contains .declPPQ = false := ⟨rfl, rfl⟩

theorem declNPQ_requires_negative_evidence :
    (czechBiasProfile .againstP .neutral).contains .declNPQ = true ∧
    (czechBiasProfile .forP .neutral).contains .declNPQ = false := ⟨rfl, rfl⟩

/-- InterNPQ has the broadest distribution among negative forms —
it appears in three bias cells, reflecting Czech outer negation's
broader distribution than English HiNQ ([simik-2024] §5). -/
theorem interNPQ_broad_distribution :
    (czechBiasProfile .forP .neutral).contains .interNPQ = true ∧
    (czechBiasProfile .neutral .forP).contains .interNPQ = true ∧
    (czechBiasProfile .againstP .forP).contains .interNPQ = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §16: DeclPQ Evidential Bias Generalization ([simik-2024] §3.2)
-- ============================================================================

/-- [simik-2024]'s key generalization: Declarative PQs are specialized for conveying
evidential bias. The polarity of the DeclPQ matches the polarity of the
evidential bias — DeclPPQ conveys positive evidential bias, DeclNPQ conveys
negative evidential bias.

Interrogative PQs, by contrast, convey epistemic bias (speaker's prior belief),
and InterNPQ can additionally convey evidential bias.

This is captured by: for any evidential bias, the DeclPQ that appears has
matching polarity. -/
theorem decl_polarity_matches_evidence :
    (czechBiasProfile .forP .neutral).contains .declPPQ = true ∧
    (czechBiasProfile .forP .againstP).contains .declPPQ = true ∧
    (czechBiasProfile .againstP .forP).contains .declNPQ = true ∧
    (czechBiasProfile .againstP .neutral).contains .declNPQ = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §17: Verb Position Readings ([stankova-2025])
-- ============================================================================

/-- Which negation readings are available for each verb position.

V1 → only outer (FALSUM) — S&Š eq. (11):
  [ForceP Q [StrengthP FALSUM[iNeg] [PolP NEG-V[uNeg] [CP … [TP SUBJECT tV …]]]]]

nonV1 → inner, medial, or outer — S&Š eq. (12), plus Staňková 2026's medial:
  [ForceP Q [StrengthP {FALSUM[iNeg]} [CP SUBJECT [TP {Op¬[iNeg]} NEG-V[uNeg] …]]]]

Note: outer negation in nonV1 requires contrastive topic on the subject
and contrastive focus on the verb (S&Š ex. 18). -/
def VerbPosition.availableReadings : VerbPosition → List NegPosition
  | .v1    => [.outer]
  | .nonV1 => [.inner, .medial, .outer]

/-- The default (unmarked) negation reading for each verb position. -/
def VerbPosition.defaultReading : VerbPosition → NegPosition
  | .v1    => .outer
  | .nonV1 => .inner

/-- V1 only allows outer negation. -/
theorem v1_only_outer :
    VerbPosition.v1.availableReadings = [NegPosition.outer] := rfl

/-- V1 default reading is outer. -/
theorem v1_default_outer :
    VerbPosition.v1.defaultReading = .outer := rfl

/-- nonV1 default reading is inner. -/
theorem nonV1_default_inner :
    VerbPosition.nonV1.defaultReading = .inner := rfl

/-- V1 default maps to HiNQ (Romero). -/
theorem v1_default_is_hiNQ :
    VerbPosition.v1.defaultReading.toPQForm = .HiNQ := rfl

/-- nonV1 default maps to LoNQ (Romero). -/
theorem nonV1_default_is_loNQ :
    VerbPosition.nonV1.defaultReading.toPQForm = .LoNQ := rfl

/-- V1 maps to InterNPQ ([simik-2024]'s finer typology). -/
theorem v1_default_is_interNPQ :
    VerbPosition.v1.defaultReading.toCzechPQForm = .interNPQ := rfl

/-- nonV1 default maps to DeclNPQ ([simik-2024]'s finer typology). -/
theorem nonV1_default_is_declNPQ :
    VerbPosition.nonV1.defaultReading.toCzechPQForm = .declNPQ := rfl

-- ============================================================================
-- §18: Context Sensitivity per Verb Position (S&Š §5.2–5.3)
-- ============================================================================

/-- Whether a verb position's default negation reading requires
contextual evidence (evidential bias) to be felicitous.

V1 (FALSUM): no — insensitive to context (S&Š §5.2, §5.3)
nonV1 (inner): yes — requires negative evidential bias (S&Š §5.2)

This is the key experimental finding of S&Š: the syntactic position
of negation determines sensitivity to contextual evidence. -/
def VerbPosition.requiresContextualEvidence : VerbPosition → Bool
  | .v1    => false  -- FALSUM = epistemic bias only
  | .nonV1 => true   -- inner neg = evidential bias

theorem v1_context_insensitive :
    VerbPosition.v1.requiresContextualEvidence = false := rfl

theorem nonV1_context_sensitive :
    VerbPosition.nonV1.requiresContextualEvidence = true := rfl

/-- Context sensitivity correlates with evidential bias strength:
V1/outer has no evidential bias requirement (FALSUM is epistemic).
nonV1/inner has strong evidential bias (requires contextual evidence for ¬p). -/
theorem context_tracks_bias_strength :
    VerbPosition.v1.defaultReading.biasStrength = .none_ ∧
    VerbPosition.nonV1.defaultReading.biasStrength = .strong := ⟨rfl, rfl⟩

-- ============================================================================
-- §19: Czech FALSUM Broader Than English (S&Š §5.3, ex. 14)
-- ============================================================================

/-- Czech outer negation (FALSUM) is compatible with all types of
evidential bias — positive, negative, and neutral — unlike English HiNQs
which require negative or neutral evidence.

This is confirmed by the positive-evidence subexperiment (S&Š ex. 14):
V1 PQs with positive evidential bias were rated very natural (median 6/7).

The broader distribution follows from Czech FALSUM being tied to
epistemic bias (speaker's possibility assessment) rather than to
evidential bias. FALSUM^CZ ([simik-2024] eq. 44) only requires that the
speaker considers p epistemically possible, regardless of evidence. -/
theorem czech_falsum_broader_than_english :
    VerbPosition.v1.requiresContextualEvidence = false ∧
    VerbPosition.v1.defaultReading.biasStrength = .none_ := ⟨rfl, rfl⟩

-- ============================================================================
-- §20: Corpus Data ([simik-2024], fn. 56)
-- ============================================================================

/-- Corpus data for *náhodou* in PQs ([simik-2024] fn. 56).

From 100 random occurrences of *náhodou* in PQs (SYN v11, Czech National Corpus):
- All 100 involved negation
- 6 had indefinite pronoun/determiners, all were PPIs (no NCIs)
- All diagnosed outer negation

This confirms the fragment-level claim that náhodou requires outer negation
and is incompatible with NCIs. -/
structure NahodouCorpusData where
  /-- Total random sample size -/
  sampleSize : Nat
  /-- Number involving negation -/
  withNegation : Nat
  /-- Number with indefinite determiners -/
  withIndefinites : Nat
  /-- Number of those indefinites that were PPIs -/
  ppiIndefinites : Nat

def nahodouCorpus : NahodouCorpusData :=
  { sampleSize := 100
  , withNegation := 100
  , withIndefinites := 6
  , ppiIndefinites := 6 }

/-- All náhodou PQ occurrences involved negation. -/
theorem nahodou_always_negated :
    nahodouCorpus.withNegation = nahodouCorpus.sampleSize := rfl

/-- All indefinites with náhodou were PPIs (no NCIs). -/
theorem nahodou_only_ppis :
    nahodouCorpus.ppiIndefinites = nahodouCorpus.withIndefinites := rfl

-- ============================================================================
-- §21: InterNPQ Use Categories ([simik-2024] §5.2)
-- ============================================================================

/-- Categories of InterNPQ use with *náhodou* ([simik-2024] §5.2, fn. 59).

From 100 random occurrences, the four main categories are:
1. Prior speaker belief (conflict-resolving PQ) — 14%
2. Explanation-seeking (no prior bias, situational evidence) — 40%
3. Relevance PQ (suggesting p is worth discussing) — 20%
4. Hope (speaker hopes p is true) — 20%
-/
inductive InterNPQUseCategory where
  /-- Conflict between prior epistemic bias for p and evidential bias for ¬p.
      The prototypical biased HiNQ use. -/
  | belief
  /-- No prior epistemic bias; evidential bias from observed situation.
      Not available in English HiNQ. -/
  | explanationSeeking
  /-- Speaker suggests p is relevant for further discussion. -/
  | relevance
  /-- Speaker hopes that p, and considers it epistemically possible. -/
  | hope
  deriving DecidableEq, Repr

/-- Distribution of InterNPQ+náhodou use categories ([simik-2024] fn. 59). -/
def interNPQDistribution : InterNPQUseCategory → Nat
  | .belief             => 14
  | .explanationSeeking => 40
  | .relevance          => 20
  | .hope               => 20

/-- Explanation-seeking is the most common InterNPQ+náhodou use.
This motivates [simik-2024]'s weaker FALSUM^CZ: the attitude holder merely
considers p epistemically possible, not that they believe p. -/
theorem explanationSeeking_most_common :
    interNPQDistribution .explanationSeeking >
    interNPQDistribution .belief := by decide

end Stankova2026
