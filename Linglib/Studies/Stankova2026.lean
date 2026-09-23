module

public import Linglib.Syntax.Category.Particle.Basic
public import Linglib.Fragments.Slavic.Czech.Particles
public import Linglib.Studies.StankovaSimik2025
public import Linglib.Studies.Simik2024
public import Linglib.Semantics.Questions.Bias
public import Linglib.Data.Examples.Stankova2026
public import Linglib.Data.Examples.StankovaSimik2025

/-!
# Czech three-way negation in polar questions (Staňková 2026)

[stankova-2026] proposes that negation in Czech polar questions occupies
three LF positions (her (16)) — outer (PolP), medial (ModP), inner (TP)
— fingerprinted by polarity items and the diagnostic particles
*náhodou* / *ještě* / *fakt* (her Table 1, `licensed`):

| Position | ne- > PPI | NCI | náhodou | ještě | fakt |
|----------|-----------|-----|---------|-------|------|
| outer    | ✓         | ✗   | ✓       | ✗     | ✗    |
| medial   | ✓         | ✗   | ✗       | ✗     | ✓    |
| inner    | ✗         | ✓   | ✗       | ✓     | ✓    |

The positions refine [simik-2024]'s two readings of negation
(`Position.ofNegation`): medial negation is the paper's addition, low
like inner negation but non-propositional like FALSUM.

## Main results

* `licensed_injective` — Table 1 fingerprints the three positions;
  `particle_signatures_distinct` — the three particle columns alone do.
* `licenses_nciLicensed_iff` and its siblings — each column
  characterized by scope; the polarity columns agree with
  [stankova-2025]'s licensing of the indefinites
  (`licenses_nciLicensed_iff_licensedAt`).
* `nahodou_identifies_outer`, `jeste_identifies_inner`,
  `fakt_plus_no_jeste_identifies_medial` — per-particle pinning.
* `czech_refines_loNQ` — Czech splits [romero-2024]'s LoNQ into inner
  and medial.
* `examples_match_table1` — the paper's examples
  (`Data.Examples.Stankova2026`) check against Table 1.

## References

* [stankova-2026], [stankova-2025], [stankova-2023], [zeijlstra-2004],
  [romero-2024], [simik-2024], [gartner-gyuris-2017].
-/

@[expose] public section

namespace Stankova2026

open Question Simik2024
open StankovaSimik2025 (VerbPosition LicensedAt)

/-! ### The three positions -/

/-- The LF positions of negation in a Czech polar question, ordered by scope width: inner
negation in TP is propositional negation, medial negation in ModP scopes over the evidential
modal, and outer negation in PolP is the commitment operator FALSUM (the paper's (16)). -/
inductive Position where
  /-- Inner negation: propositional ¬p in TP, licensing negative concord items by Agree
      ([zeijlstra-2004]). -/
  | inner
  /-- Medial negation: over the evidential modal in ModP, part of the bias presupposition. -/
  | medial
  /-- Outer negation: FALSUM in PolP, high negation with obligatory focus. -/
  | outer
  deriving DecidableEq, Repr, Fintype

/-- [simik-2024]'s two readings as positions: inner and outer negation. -/
def Position.ofNegation : Negation → Position
  | .inner => .inner
  | .outer => .outer

/-- The evidential bias strength of a negation position (the paper's §3.1): inner negation
presupposes evidence for ¬p, medial negation only the absence of evidence for p, and FALSUM
conveys epistemic rather than evidential bias. -/
inductive BiasStrength where
  | strong
  | weak
  | none_
  deriving DecidableEq, Repr

/-- The evidential bias strength of each position. -/
def Position.biasStrength : Position → BiasStrength
  | .inner => .strong
  | .medial => .weak
  | .outer => .none_

/-! ### Table 1 -/

/-- The Table 1 diagnostics of a negation position. -/
inductive Diagnostic where
  /-- The negation admits a positive polarity item like *nějaký* 'some' in its scope. -/
  | ppiOutscoping
  /-- The negation licenses a negative concord item like *žádný* 'no'. -/
  | nciLicensed
  /-- The particle *náhodou* 'by chance' is compatible. -/
  | nahodou
  /-- The particle *ještě* 'yet, still' is compatible. -/
  | jeste
  /-- The particle *fakt* 'really' is compatible. -/
  | fakt
  deriving DecidableEq, Repr, Fintype

/-- Table 1: the diagnostics each negation position licenses. -/
def licensed : Position → Finset Diagnostic
  | .inner => {.nciLicensed, .jeste, .fakt}
  | .medial => {.ppiOutscoping, .fakt}
  | .outer => {.ppiOutscoping, .nahodou}

/-- A cell of Table 1: the position licenses the diagnostic. -/
abbrev Licenses (pos : Position) (d : Diagnostic) : Prop := d ∈ licensed pos

/-- Table 1 fingerprints the positions: no two license the same diagnostics. -/
theorem licensed_injective : Function.Injective licensed := by decide

variable {pos : Position}

/-- Only propositional negation licenses a concord item, by Agree with the operator. -/
theorem licenses_nciLicensed_iff : Licenses pos .nciLicensed ↔ pos = .inner := by
  cases pos <;> decide

/-- Every non-propositional negation admits a positive polarity item. -/
theorem licenses_ppiOutscoping_iff : Licenses pos .ppiOutscoping ↔ pos ≠ .inner := by
  cases pos <;> decide

/-- *Náhodou* singles out FALSUM. -/
theorem licenses_nahodou_iff : Licenses pos .nahodou ↔ pos = .outer := by
  cases pos <;> decide

/-- *Ještě* singles out propositional negation. -/
theorem licenses_jeste_iff : Licenses pos .jeste ↔ pos = .inner := by
  cases pos <;> decide

/-- *Fakt* is repelled by FALSUM alone. -/
theorem licenses_fakt_iff : Licenses pos .fakt ↔ pos ≠ .outer := by
  cases pos <;> decide

/-- On the two readings of [simik-2024], the concord column of Table 1 is
[stankova-2025]'s licensing of *žádný*. -/
theorem licenses_nciLicensed_iff_licensedAt (n : Negation) :
    Licenses (.ofNegation n) .nciLicensed ↔ LicensedAt StankovaSimik2025.Indefinite.nci.entry n := by
  cases n <;> decide

/-- On the two readings of [simik-2024], the polarity column of Table 1 is
[stankova-2025]'s licensing of *nějaký*. -/
theorem licenses_ppiOutscoping_iff_licensedAt (n : Negation) :
    Licenses (.ofNegation n) .ppiOutscoping ↔
      LicensedAt StankovaSimik2025.Indefinite.ppi.entry n := by
  cases n <;> decide

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

/-- Table 1 compatibility of a particle with a negation position: the position licenses
the particle's diagnostic, vacuously for a particle outside the table. -/
def Compatible (p : Particle) (pos : Position) : Prop :=
  ∀ d ∈ diagnostic? p, Licenses pos d

instance (p : Particle) (pos : Position) : Decidable (Compatible p pos) := by
  unfold Compatible; infer_instance

/-- *náhodou* uniquely identifies outer negation. -/
theorem nahodou_identifies_outer (pos : Position) : Compatible nahodou pos → pos = .outer := by
  cases pos <;> decide

/-- *ještě* uniquely identifies inner negation. -/
theorem jeste_identifies_inner (pos : Position) : Compatible jeste pos → pos = .inner := by
  cases pos <;> decide

/-- *fakt* accepted while *ještě* is rejected identifies medial
negation. -/
theorem fakt_plus_no_jeste_identifies_medial (pos : Position) :
    Compatible fakt pos ∧ ¬ Compatible jeste pos → pos = .medial := by
  cases pos <;> decide

/-- The three Table 1 particles jointly fingerprint the three negation
positions. -/
theorem particle_signatures_distinct (pos pos' : Position)
    (h : ∀ p ∈ [nahodou, jeste, fakt], Compatible p pos ↔ Compatible p pos') : pos = pos' := by
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
[stankova-2026] §1). The `VerbPosition` API lives with the experiment
that established it, in `StankovaSimik2025`. Crossing word order with
polarity gives [simik-2024]'s 2×2 grid of PQ forms (`Simik2024.CzechPQForm`),
which maps onto [romero-2024]'s PosQ/LoNQ/HiNQ typology. -/

/-- [romero-2024] PQ form of a negation position: outer is high
negation (HiNQ), inner and medial are both low (LoNQ). -/
def Position.toPQForm : Position → PQForm
  | .inner | .medial => .LoNQ
  | .outer => .HiNQ

/-- Only outer negation (FALSUM) is obligatorily focused
([stankova-2026] §3.2). -/
def Position.RequiresFocus : Position → Prop
  | .outer => True
  | .medial | .inner => False

instance : DecidablePred Position.RequiresFocus := fun pos => by
  cases pos <;> unfold Position.RequiresFocus <;> infer_instance

/-- Verb position realizing a negation position: outer is V1, inner and
medial are nonV1. -/
def Position.toVerbPosition : Position → VerbPosition
  | .inner | .medial => .nonV1
  | .outer => .v1

/-- [simik-2024] PQ form of a negation position: outer is InterNPQ,
inner and medial are DeclNPQ. -/
def Position.toCzechPQForm : Position → CzechPQForm
  | .inner | .medial => .declNPQ
  | .outer => .interNPQ

/-- The two form typologies agree: [simik-2024]'s grid refines
[romero-2024]'s. -/
theorem czechPQForm_consistent_with_pqForm :
    ∀ pos : Position, pos.toCzechPQForm.toPQForm = pos.toPQForm := by
  intro pos; cases pos <;> rfl

/-- Czech refines [romero-2024]'s LoNQ: inner and medial share the LoNQ
form but differ in evidential bias strength and in Table 1
signatures. -/
theorem czech_refines_loNQ :
    Position.inner.toPQForm = Position.medial.toPQForm ∧
    Position.inner.biasStrength ≠ Position.medial.biasStrength ∧
    licensed .inner ≠ licensed .medial :=
  ⟨rfl, by decide, by decide⟩

/-- Obligatory focus singles out outer negation ([stankova-2026]
§3.2). -/
theorem only_outer_requires_focus (p : Position) : p.RequiresFocus → p = .outer := by
  cases p <;> simp [Position.RequiresFocus]

/-! ### Verb position and context sensitivity

The verb-position API (`availableReadings`, `defaultReading`) is
[stankova-2025]'s and lives in `StankovaSimik2025`; this paper adds
the link to evidential bias strength. -/

/-- Context sensitivity tracks evidential bias strength: V1/outer none,
nonV1/inner strong. -/
theorem context_tracks_bias_strength :
    (Position.ofNegation VerbPosition.v1.defaultReading).biasStrength = .none_ ∧
    (Position.ofNegation VerbPosition.nonV1.defaultReading).biasStrength = .strong :=
  ⟨rfl, rfl⟩

/-! ### The paper's examples

Typed stimuli live in `Data.Examples.Stankova2026`; each is paired here
with the negation reading and Table 1 diagnostic the paper assigns. -/

open Data.Examples (LinguisticExample)

/-- The paper's polarity/particle examples with their negation reading
and tested diagnostic. -/
def analyzedExamples : List (LinguisticExample × Position × Diagnostic) :=
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
    ∀ x ∈ analyzedExamples, x.1.judgment = .acceptable ↔ Licenses x.2.1 x.2.2 := by decide

/-- [stankova-2025]'s positive-evidence stimulus ((14): V1 negative PQ
after evidence for p) with the bias-profile cell it occupies. -/
def biasCheckedExamples :
    List (LinguisticExample × Option Polarity × Option Polarity × CzechPQForm) :=
  [ (StankovaSimik2025.Examples.ex14, some .positive, none, .interNPQ) ]

/-- The bias profile predicts the positive-evidence stimulus — the form
is felicitous iff it appears in its evidence × original-bias cell. -/
theorem bias_examples_match_profile :
    ∀ x ∈ biasCheckedExamples,
      x.1.judgment = .acceptable ↔ x.2.2.2 ∈ czechBiasProfile x.2.1 x.2.2.1 := by
  decide

end Stankova2026
