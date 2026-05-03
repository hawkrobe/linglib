import Linglib.Core.Case.Basic
import Linglib.Theories.Interfaces.Morphosyntax.Extraction
import Linglib.Fragments.Mayan.Params

/-!
# Chol Agreement and Case Fragment @cite{coon-2013} @cite{imanishi-2020}

Agreement morphology and case assignment for Chol (Cholan, Mayan), a
**low absolutive** language with aspect-based split alignment. Per
@cite{vazquez-alvarez-2011} §1.9.4, Chol is "an ergative
language" in which "the ergative pattern is split in all non-perfective
aspects, resulting in nominative-accusative alignment" — Set A indicates
both transitive and intransitive subjects in non-perfective.

## Descriptive vs analytical framing of the non-perfective pattern

The descriptive grammar (@cite{vazquez-alvarez-2011}) characterizes the
non-perfective alignment as **nominative-accusative**: Set A as a
nominative-like marker grouping S with A, Set B as accusative on O.

The formal-syntactic analyses cited here label the same surface pattern
differently: @cite{coon-2013} argues the non-perfective construction
embeds a nominalized clause (with the aspectual predicate *choñkol* as
matrix), so Set A on the embedded subject is genitive-from-D, NOT
nominative — the morphological identity of Set A with the possessive
marker (cf. `tyi j-kajpelo` 'in my coffee field' vs `tyi j-k'el-e-ø`
'I saw him', both with Set A `j-` per @cite{vazquez-alvarez-2011}
p. 76) is taken as evidence. @cite{imanishi-2020} parameterizes Mayan
split-ergative alignment via two parameters: (i) the Restriction on
Nominalization (RON) on the nominalizing head *n*, and (ii) the Mayan
Absolutive Parameter (high vs low ABS, after
@cite{coon-mateo-pedro-preminger-2014}). For Chol, *n* does not impose
RON, so S/A is the highest DP in the nominalized clause and receives
genitive from D — matching Coon's analytical view. The substrate's
`extendedErgative.assignCase` returns `.gen` (Coon's analytical view);
a descriptive-grammar implementation would return `.nom`. The label
"extended ergative" is Coon's coinage, generalizing one subtype of
@cite{dixon-1994}'s split-ergative-on-TAM-lines pattern.

## Morpheme order and word-class status

Per @cite{vazquez-alvarez-2011} §3.4: in Chol "the aspect
markers are auxiliaries" — `tyi` (perfective) and `mi` (imperfective)
are **aspectual auxiliaries** (independent words preceding the verbal
complex), not particles, not clitics, not verbal prefixes. Set A
ergative/genitive markers are prefixes on the verbal complex (per
@cite{vazquez-alvarez-2011} §4.1.1; some prior literature treats them
as proclitics — @cite{martinez-cruz-2007}, @cite{arcos-lopez-2009}).
Set B absolutive markers are suffixes (per @cite{kaufman-norman-1984}
p. 90, originally cliticized pronouns).

Schematic order: `[Aux] [ERG-modifier*-ROOT-DERIV-STATUS-ABS]`, with
the bracketed verbal complex as a single phonological unit. Contrasts
with Kaqchikel's `[Aux] [ABS-ERG-Stem]` (high-ABS).

## The Two Agreement Paradigms (Set A / Set B)

- **Set A** (ergative in perfective; nominative-or-genitive in
  non-perfective; possessive on nominals): prefixes
- **Set B** (absolutive in perfective; accusative in non-perfective):
  suffixes

## Case Licensing (analytical, per @cite{coon-2013})

- **ERG**: inherent from transitive *v*
- **ABS** (transitive): structural from Voice (low absolutive)
- **ABS** (intransitive): structural from Infl
- **GEN** (non-perfective S/A): from D under nominalization

## Accusative Side (Non-Perfective)

In non-perfective aspect, the aspectual predicate *choñkol* embeds a
nominalized clause. The RON does NOT hold: the external argument may be
generated inside the nominalized clause. Result (Coon analysis):
S/A = GEN (from D), O = ABS (from Voice).

## What this fragment doesn't model

Per @cite{vazquez-alvarez-2011} §1.9.4, Chol exhibits all
four Dixon alignment types: ergative-absolutive, nominative-accusative, **Split-S**
(some intransitives obligatorily Sa = Set A on light verb *cha'l*; others
obligatorily So = Set B), and **Fluid-S** (verbs like *wäy* 'sleep' that
take either Set A or Set B). The current `ArgPosition.intranS` collapses
Sa/So/fluid-S into a single intransitive subject category — sufficient
for the perfective↔non-perfective split formalization but undermodels
the agentive split. Future refinement: split into `intranSAgentive` /
`intranSPatientive` / `intranSFluid`.
-/

namespace Fragments.Mayan.Chol

open Fragments.Mayan (PersonNumber)

-- ============================================================================
-- § 1: Argument Positions (alias to canonical SAP type)
-- ============================================================================

/-- Argument positions in a Chol clause. Aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) so cross-Mayan and
    cross-framework code shares one inventory. Use the canonical
    constructor names `.A` / `.P` / `.S` directly. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Perfective case assignment for Chol. Definitionally equal to
    `Fragments.Mayan.ergCaseChol`, which derives from
    `Alignment.ergative.assignCase` in
    `Theories/Syntax/Case/Alignment.lean` — the foundation makes the
    pattern (A → ERG, S/P → ABS) explicit; the per-language wrapper
    preserves dot-notation `position.case` for consumers, uniform
    with the other Mayan fragments. -/
abbrev ArgPosition.case : ArgPosition → Core.Case := Fragments.Mayan.ergCaseChol

/-- Non-perfective case assignment for Chol. Definitionally equal to
    `Fragments.Mayan.accCaseChol`, derived from
    `Alignment.extendedErgative.assignCase`. The "extended ergative"
    pattern (S/A → GEN, P → ABS) is shared with Q'anjob'al — both
    fragments call into the same `caseExtErg` substrate. -/
abbrev ArgPosition.accCase : ArgPosition → Core.Case := Fragments.Mayan.accCaseChol

-- ============================================================================
-- § 2: Absolutive Position (LOW-ABS)
-- ============================================================================

/-- Chol's absolutive morphemes appear in low position (at the end of
    the verb stem, post-stem). Observable from morpheme order:
    ASP-ERG-ROOT-(DERIV)-SUFFIX-ABS. -/
def absPosition : Fragments.Mayan.ABSPosition := .low

-- ============================================================================
-- § 3: Extraction Data
-- ============================================================================

/-- Chol's extraction profile: no special morphology for any extraction.
    Unlike Q'anjob'al, Chol requires **no Agent Focus morphology** for
    A-extraction (the diagnostic for "lacking syntactic ergativity" in the
    @cite{coon-mateo-pedro-preminger-2014} sense). The substantive claim
    is `extractionProfile.strategy = .none`; per-position extractability
    follows trivially (every argument extracts freely), so no per-position
    table is stipulated — the contrast with Q'anjob'al lives at the
    `strategy` field.

    The resulting ambiguity (when both arguments are 3rd person) is a
    natural consequence of the absence of AF marking:
    `Maxki₁ tyi y-il-ä (___₁) jiñi wiñik (___₁)?`
    'Who saw the man?' / 'Who did the man see?' -/
def extractionProfile : Interfaces.ExtractionProfile :=
  { language := "Chol"
  , strategy := .none
  , markedPositions := []
  , distinguishesPosition := false
  , notes := "No Agent Focus morphology required for A-extraction @cite{coon-mateo-pedro-preminger-2014}" }

-- ============================================================================
-- § 4: Non-Finite Absolutive Availability
-- ============================================================================

/-- In Chol non-finite embedded clauses (aspectless), absolutive objects
    ARE available. This follows from Chol being LOW-ABS: v⁰ assigns case
    to the object without needing Infl⁰.

    `Mejl [i-k'el-oñ]` 'She can see me.' (ABS object ✓)
    `Choñkol [k-mek'-ety]` 'I am hugging you.' (ABS object ✓) -/
def absObjectInNonFinite : Bool := true

/-- Absolutive intransitive subjects are NOT available in Chol non-finite
    clauses: they must be marked with the ergative/possessive prefix instead.

    `Choñkol [k-ts'äm-el]` 'I am bathing.' (ERG prefix, not ABS)
    `*Choñkol [ts'äm-i-yoñ]` intended: 'I am bathing.' (ABS ✗) -/
def absIntranSInNonFinite : Bool := false

-- ============================================================================
-- § 5: Person-Number Paradigm (Tables 9-10 of @cite{vazquez-alvarez-2011})
-- ============================================================================

/-- Set A (ergative/possessive/genitive) markers: pre-consonantal allomorphs
    (@cite{vazquez-alvarez-2011} Table 10, p. 83). Note the morphophonemic
    rule k- → j- /_k (1sg before a /k/ root, e.g., `tyi j-kajpelo`
    'in my coffee field' p. 76). Plural forms use the inclusive clitic
    `=la` for 1pl (the unmarked plural form per VA §4.2); the exclusive
    paradigm with `=l(oj)oñ` is a per-language refinement not exposed
    by the pan-Mayan `PersonNumber` substrate. -/
def setAExponentPreC : PersonNumber → String
  | .p1sg => "k-"
  | .p2sg => "a-"
  | .p3sg => "i-"
  | .p1pl => "k-…=la"
  | .p2pl => "a-…=la"
  | .p3pl => "i-…-ob"

/-- Set A markers: pre-vocalic allomorphs (@cite{vazquez-alvarez-2011}
    Table 10, p. 83). 1sg `k-` is identical pre-C and pre-V; 2sg surfaces
    as `aw-`, 3sg as `(i)y-` (some speakers omit the initial vowel —
    @cite{vazquez-alvarez-2011} examples (12)-(13) p. 76-77). -/
def setAExponentPreV : PersonNumber → String
  | .p1sg => "k-"
  | .p2sg => "aw-"
  | .p3sg => "(i)y-"
  | .p1pl => "k-…=la"
  | .p2pl => "aw-…=la"
  | .p3pl => "(i)y-…-ob"

/-- Canonical Set A exponent table for cross-Mayan typology. The
    pre-consonantal allomorph is the citation form (matching Q'anjob'al's
    convention); per-context realization uses `setAExponentPreV` before
    vowel-initial roots. -/
abbrev setAExponent : PersonNumber → String := setAExponentPreC

/-- Set B (absolutive) markers: suffixes (@cite{vazquez-alvarez-2011}
    Table 10, p. 83). 3rd person is null (`-∅`). Plurals use the
    inclusive `=la` clitic for 1pl per the convention above. -/
def setBExponent : PersonNumber → String
  | .p1sg => "-oñ"
  | .p2sg => "-ety"
  | .p3sg => "-∅"
  | .p1pl => "-oñ=la"
  | .p2pl => "-ety=la"
  | .p3pl => "-∅-ob"

/-- 3rd person absolutive is null — invariant across the standard
    Mayan branches (Cholan, Q'anjob'alan, Tseltalan, K'ichean) per
    @cite{kaufman-norman-1984} Table 8 reconstruction. **Not** universally
    pan-Mayan: Mam's default Set B `tz'=` surfaces in the 3sg slot
    (@cite{scott-2023}), and `MayanLang.isStandard` excludes Mam from
    the relevant cross-Mayan theorem (`mayan_p3sg_abs_null`). -/
theorem p3sg_abs_null : setBExponent .p3sg = "-∅" := rfl

/-- 3rd person Set A allomorphy: pre-consonantal `i-` vs pre-vocalic
    `(i)y-`. Distinct from Q'anjob'al's `s-` vs `y-` (the proto-Mayan
    `*s-` ~ `*y-` allomorphy was leveled to `*r` → `y` in proto-Tseltalan,
    and Chol inherited the leveled form per @cite{kaufman-norman-1984}
    p. 91). -/
theorem p3sg_erg_allomorphy :
    setAExponentPreC .p3sg = "i-" ∧ setAExponentPreV .p3sg = "(i)y-" :=
  ⟨rfl, rfl⟩

end Fragments.Mayan.Chol
