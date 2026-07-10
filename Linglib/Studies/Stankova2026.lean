import Linglib.Syntax.Category.Particle.Capabilities
import Linglib.Fragments.Slavic.Czech.Particles
import Linglib.Semantics.Negation.CzechNegation
import Linglib.Studies.StankovaSimik2025
import Linglib.Semantics.Questions.Bias
import Linglib.Data.Examples.Stankova2026

/-!
# Czech three-way negation in polar questions (Staňková 2026)

[stankova-2026] proposes that negation in Czech polar questions occupies
three LF positions (her (16)) — outer (PolP), medial (ModP), inner (TP)
— fingerprinted by polarity items and the diagnostic particles
*náhodou* / *ještě* / *fakt* (her Table 1, encoded as the substrate's
`licenses`):

| Position | ne- > PPI | NCI | náhodou | ještě | fakt |
|----------|-----------|-----|---------|-------|------|
| outer    | ✓         | ✗   | ✓       | ✗     | ✗    |
| medial   | ✓         | ✗   | ✗       | ✗     | ✓    |
| inner    | ✗         | ✓   | ✗       | ✓     | ✓    |

## Main results

* `signatures_distinct`, `particle_signatures_distinct` — the Table 1
  columns jointly fingerprint the three positions.
* `nahodou_identifies_outer`, `jeste_identifies_inner`,
  `fakt_plus_no_jeste_identifies_medial` — per-particle pinning.
* `instance Distributed Particle NegPosition` — Table 1 as a licensing
  axis alongside clause type and embedding.
* `czech_refines_loNQ` — Czech splits [romero-2024]'s LoNQ into inner
  and medial.
* `czechBiasProfile` — [simik-2024]'s Table 2 grid of PQ forms by
  evidential × original bias.
* `examples_match_table1` — the paper's examples
  (`Data.Examples.Stankova2026`) check against Table 1.

## References

* [stankova-2026], [stankova-2025], [stankova-2023], [zeijlstra-2004],
  [romero-2024], [simik-2024], [gartner-gyuris-2017].
-/

namespace Stankova2026

open Semantics.Negation.CzechNegation

/-! ### Table 1 fingerprints -/

/-- The Boolean signature of a negation position across the five
Table 1 diagnostics. -/
def signature (pos : NegPosition) : List Bool :=
  [ licenses pos .ppiOutscoping
  , licenses pos .nciLicensed
  , licenses pos .nahodou
  , licenses pos .jeste
  , licenses pos .fakt ]

/-- Each negation position has a unique diagnostic signature — the
empirical basis for the three-way distinction. -/
theorem signatures_distinct :
    signature .outer ≠ signature .medial ∧
    signature .outer ≠ signature .inner ∧
    signature .medial ≠ signature .inner := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold signature licenses; decide)

/-- Only inner negation licenses NCIs: the Agree relation with `¬`
requires LF c-command, and medial and outer negation are too high
([stankova-2026] (6), (10)). -/
theorem only_inner_licenses_nci :
    ∀ p : NegPosition, licenses p .nciLicensed = true → p = .inner := by
  intro p h; cases p <;> simp_all [licenses]

/-! ### The diagnostic particles ([stankova-2026] §2.2, Table 1)

Entries live in `Czech.Particles`; this paper contributes the §2.2
licensing profiles — *ještě* felicitous in PQs only under inner
negation (§2.2.2, (14); with telic predicates it requires negation,
(13)), *fakt* licensed by inner and medial but repelled by outer on its
canonical reading (§2.2.3, (15), fn. 8), *vůbec* an NPI licensed by
inner only ((9)-(10)) — plus the Table 1 assignments and the
fingerprint results. -/

open Czech.Particles (nahodou jeste fakt vubec snad copak)
open StankovaSimik2025 (ParticleSemantics)

/-- This paper's classification of its three particles (the others are
classified in `StankovaSimik2025.classification`). The paper defers
*fakt*'s semantics, noting the parallels to English *really* (Romero &
Han's VERUM) and Russian *razve*. -/
def classification : List (Particle × ParticleSemantics) :=
  [(jeste, .temporalEndpoint), (fakt, .veridicalEmphasis), (vubec, .npi)]

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

/-- The three Table 1 particles jointly fingerprint the three negation
positions. -/
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

/-! ### Word order and PQ-form typology

Czech PQs come in V1 (interrogative) and nonV1 (declarative) word
orders; since *ne-* is inseparable from the finite verb, verb position
determines the syntactic position of negation ([stankova-2025] §2,
[stankova-2026] §1). Crossing word order with polarity gives
[simik-2024]'s 2×2 grid of PQ forms, which maps onto [romero-2024]'s
PosQ/LoNQ/HiNQ typology. -/

/-- Verb position in Czech PQs: V1 (interrogative word order, verb+ne-
high) vs nonV1 (declarative word order, verb+ne- in TP). -/
inductive VerbPosition where
  | v1
  | nonV1
  deriving DecidableEq, Repr

/-- [simik-2024]'s 2×2 grid of Czech PQ forms ([simik-2024] §3.2,
exx. 11-17): word order (interrogative vs declarative) × polarity. -/
inductive CzechPQForm where
  /-- Interrogative (V1), positive: the default unbiased PQ. -/
  | interPPQ
  /-- Interrogative (V1), negative: outer negation, positive epistemic
      bias; broader distribution than English HiNQ ([simik-2024] §5). -/
  | interNPQ
  /-- Declarative (nonV1), positive: positive evidential bias. -/
  | declPPQ
  /-- Declarative (nonV1), negative: negative evidential bias. -/
  | declNPQ
  deriving DecidableEq, Repr

end Stankova2026

namespace Semantics.Negation.CzechNegation

open Semantics.Questions.Bias
open Stankova2026 (VerbPosition CzechPQForm)

/-- [romero-2024] PQ form of a negation position: outer is high
negation (HiNQ), inner and medial are both low (LoNQ). -/
def NegPosition.toPQForm : NegPosition → PQForm
  | .inner | .medial => .LoNQ
  | .outer => .HiNQ

/-- Evidential bias strength of a negation position ([stankova-2026]
§3.1): inner strong, medial weak, outer none (FALSUM is
epistemic-bias-based). -/
def NegPosition.biasStrength : NegPosition → EvidentialBiasStrength
  | .inner  => .strong
  | .medial => .weak
  | .outer  => .none_

/-- Only outer negation (FALSUM) is obligatorily focused
([stankova-2026] §3.2). -/
def NegPosition.requiresFocus : NegPosition → Bool
  | .outer => true
  | .medial | .inner => false

/-- Verb position realizing a negation position: outer is V1, inner and
medial are nonV1. -/
def NegPosition.toVerbPosition : NegPosition → VerbPosition
  | .inner | .medial => .nonV1
  | .outer => .v1

/-- [simik-2024] PQ form of a negation position: outer is InterNPQ,
inner and medial are DeclNPQ. -/
def NegPosition.toCzechPQForm : NegPosition → CzechPQForm
  | .inner | .medial => .declNPQ
  | .outer => .interNPQ

end Semantics.Negation.CzechNegation

namespace Stankova2026

open Semantics.Negation.CzechNegation
open Semantics.Questions.Bias

/-- [romero-2024] PQ form of each [simik-2024] grid cell: InterNPQ is
HiNQ, DeclNPQ is LoNQ, positive forms are PosQ. -/
def CzechPQForm.toPQForm : CzechPQForm → PQForm
  | .interPPQ | .declPPQ => .PosQ
  | .interNPQ => .HiNQ
  | .declNPQ  => .LoNQ

/-- The two form typologies agree: [simik-2024]'s grid refines
[romero-2024]'s. -/
theorem czechPQForm_consistent_with_pqForm :
    ∀ pos : NegPosition, pos.toCzechPQForm.toPQForm = pos.toPQForm := by
  intro pos; cases pos <;> rfl

/-- Czech refines [romero-2024]'s LoNQ: inner and medial share the LoNQ
form but differ in evidential bias strength and in their Table 1
signatures. -/
theorem czech_refines_loNQ :
    NegPosition.inner.toPQForm = NegPosition.medial.toPQForm ∧
    NegPosition.inner.biasStrength ≠ NegPosition.medial.biasStrength ∧
    signature .inner ≠ signature .medial :=
  ⟨rfl, by decide, by (unfold signature licenses; decide)⟩

/-- Obligatory focus singles out outer negation ([stankova-2026]
§3.2). -/
theorem only_outer_requires_focus :
    ∀ p : NegPosition, p.requiresFocus = true → p = .outer := by
  intro p h; cases p <;> simp_all [NegPosition.requiresFocus]

/-- Czech outer negation is a HiNQ with mandatory original bias for p,
matching [romero-2024]'s Table 1. -/
theorem czech_outer_matches_romero_hiNQ_bias :
    NegPosition.outer.toPQForm = .HiNQ ∧
    originalBiasOK .HiNQ .forP = true ∧
    originalBiasOK .HiNQ .neutral = false := ⟨rfl, rfl, rfl⟩

/-- Czech low negation is a LoNQ compatible with neutral original bias,
matching [romero-2024]'s Table 1. -/
theorem czech_low_neg_matches_romero_loNQ_bias :
    NegPosition.inner.toPQForm = .LoNQ ∧
    originalBiasOK .LoNQ .neutral = true := ⟨rfl, rfl⟩

/-- Czech inner negation requires contextual evidence against p,
matching [romero-2024]'s Table 2 for LoNQs. -/
theorem czech_inner_matches_romero_evidence_bias :
    NegPosition.inner.toPQForm = .LoNQ ∧
    evidenceBiasOK .LoNQ .againstP = true := ⟨rfl, rfl⟩

/-- Czech outer negation (HiNQ) is compatible with evidence against p
(contradiction scenarios). -/
theorem czech_outer_matches_romero_evidence :
    NegPosition.outer.toPQForm = .HiNQ ∧
    evidenceBiasOK .HiNQ .againstP = true := ⟨rfl, rfl⟩

/-! ### Verb position and context sensitivity -/

/-- Negation readings available per verb position ([stankova-2025]
eqs. 11-12 with [stankova-2026]'s medial added): V1 only outer; nonV1
all three (outer in nonV1 needs contrastive topic + focused verb,
[stankova-2025] ex. 18). -/
def VerbPosition.availableReadings : VerbPosition → List NegPosition
  | .v1    => [.outer]
  | .nonV1 => [.inner, .medial, .outer]

/-- The default (unmarked) negation reading per verb position. -/
def VerbPosition.defaultReading : VerbPosition → NegPosition
  | .v1    => .outer
  | .nonV1 => .inner

/-- Whether a verb position's default reading requires contextual
evidence ([stankova-2025] §5): V1 (FALSUM) is context-insensitive —
compatible with positive, negative, and neutral evidential bias, unlike
English HiNQs — while nonV1 (inner) requires negative evidential
bias. -/
def VerbPosition.requiresContextualEvidence : VerbPosition → Bool
  | .v1    => false
  | .nonV1 => true

/-- Context sensitivity tracks evidential bias strength: V1/outer none,
nonV1/inner strong. -/
theorem context_tracks_bias_strength :
    VerbPosition.v1.defaultReading.biasStrength = .none_ ∧
    VerbPosition.nonV1.defaultReading.biasStrength = .strong := ⟨rfl, rfl⟩

/-! ### The Czech bias profile ([simik-2024] Table 2) -/

/-- Which Czech PQ forms are felicitous per contextual evidence ×
original speaker bias cell ([simik-2024] Table 2, based on
[stankova-2023]); empty list = no form natural. -/
def czechBiasProfile : ContextualEvidence → OriginalBias → List CzechPQForm
  | .forP,     .forP      => []
  | .forP,     .neutral   => [.declPPQ, .interNPQ]
  | .forP,     .againstP  => [.declPPQ]
  | .neutral,  .forP      => [.interPPQ, .interNPQ]
  | .neutral,  .neutral   => [.interPPQ]
  | .neutral,  .againstP  => []
  | .againstP, .forP      => [.declNPQ, .interNPQ]
  | .againstP, .neutral   => [.declNPQ]
  | .againstP, .againstP  => []

/-- InterPPQ is the sole form felicitous with no bias at all — the
default PQ ([simik-2024] §4.1, ex. 25). -/
theorem interPPQ_is_default :
    (czechBiasProfile .neutral .neutral).contains .interPPQ = true := rfl

/-- DeclPPQ needs positive contextual evidence ([stankova-2023],
[simik-2024] §3.2). -/
theorem declPPQ_requires_positive_evidence :
    (czechBiasProfile .forP .neutral).contains .declPPQ = true ∧
    (czechBiasProfile .againstP .neutral).contains .declPPQ = false := ⟨rfl, rfl⟩

/-- DeclNPQ needs negative contextual evidence ([stankova-2023],
[simik-2024] §3.2). -/
theorem declNPQ_requires_negative_evidence :
    (czechBiasProfile .againstP .neutral).contains .declNPQ = true ∧
    (czechBiasProfile .forP .neutral).contains .declNPQ = false := ⟨rfl, rfl⟩

/-- InterNPQ appears in three bias cells — the broadest distribution
among negative forms, reflecting Czech outer negation's broader range
than English HiNQ ([simik-2024] §5). -/
theorem interNPQ_broad_distribution :
    (czechBiasProfile .forP .neutral).contains .interNPQ = true ∧
    (czechBiasProfile .neutral .forP).contains .interNPQ = true ∧
    (czechBiasProfile .againstP .forP).contains .interNPQ = true := ⟨rfl, rfl, rfl⟩

/-! ### The paper's examples

Typed stimuli live in `Data.Examples.Stankova2026`; each is paired here
with the negation reading and Table 1 diagnostic the paper assigns. -/

open Data.Examples (LinguisticExample)

/-- The paper's polarity/particle examples with their negation reading
and tested diagnostic. -/
def analyzedExamples : List (LinguisticExample × NegPosition × Diagnostic) :=
  [ (Examples.ex6a,  .inner,  .nciLicensed)
  , (Examples.ex6b,  .outer,  .nciLicensed)
  , (Examples.ex7a,  .medial, .ppiOutscoping)
  , (Examples.ex7b,  .outer,  .ppiOutscoping)
  , (Examples.ex11,  .outer,  .nahodou)
  , (Examples.ex15a, .inner,  .fakt)
  , (Examples.ex15d, .outer,  .fakt) ]

/-- Table 1 predicts each example's judgment: the diagnostic is
licensed at the example's negation position iff the example is
acceptable. -/
theorem examples_match_table1 :
    analyzedExamples.all (fun (e, pos, d) =>
      (e.judgment == .acceptable) == licenses pos d) = true := by decide

end Stankova2026
