import Linglib.Features.Case.Basic
import Linglib.Features.Reflex
import Linglib.Syntax.Extraction
import Linglib.Fragments.Mayan.Params

/-!
# Chol Agreement and Case Fragment

Agreement morphology and case assignment for Chol (Cholan, Mayan), a
**low absolutive** language with aspect-based split alignment. Per
[vazquez-alvarez-2011] §1.9.4, Chol is "an ergative language" in which
"the ergative pattern is split in all non-perfective aspects, resulting in
nominative-accusative alignment" — Set A indicates both transitive and
intransitive subjects in non-perfective. The formal-syntactic analyses of
[coon-2013] and [imanishi-2020] reanalyse this surface pattern.

## Main declarations

* `Chol.ArgPosition` with `.case`, `.accCase`: argument positions and
  their perfective (ergative) and non-perfective (extended-ergative) case.
* `Chol.absPosition`: LOW-ABS morpheme placement.
* `Chol.setAExponent`, `Chol.setBExponent`: the Set A (ERG/GEN) and Set B
  (ABS) exponent tables ([vazquez-alvarez-2011] Table 10).
* `Chol.Extraction.realize`, `Chol.absObjectInNonFinite`,
  `Chol.absIntranSInNonFinite`: the (unmarked) extraction marking and
  non-finite absolutive availability.

## Implementation notes

### Descriptive vs analytical framing of the non-perfective pattern

The descriptive grammar ([vazquez-alvarez-2011]) characterizes the
non-perfective alignment as **nominative-accusative**: Set A as a
nominative-like marker grouping S with A, Set B as accusative on O.

The formal-syntactic analyses cited here label the same surface pattern
differently: [coon-2013] argues the non-perfective construction
embeds a nominalized clause (with the aspectual predicate *choñkol* as
matrix), so Set A on the embedded subject is genitive-from-D, NOT
nominative — the morphological identity of Set A with the possessive
marker (cf. `tyi j-kajpelo` 'in my coffee field' vs `tyi j-k'el-e-ø`
'I saw him', both with Set A `j-` per [vazquez-alvarez-2011]
p. 76) is taken as evidence. [imanishi-2020] parameterizes Mayan
split-ergative alignment via two parameters: (i) the Restriction on
Nominalization (RON) on the nominalizing head *n*, and (ii) the Mayan
Absolutive Parameter (high vs low ABS, after
[coon-mateo-pedro-preminger-2014]). For Chol, *n* does not impose
RON, so S/A is the highest DP in the nominalized clause and receives
genitive from D — matching Coon's analytical view. The substrate's
`extendedErgative.assignCase` returns `.gen` (Coon's analytical view);
a descriptive-grammar implementation would return `.nom`. The label
"extended ergative" is Coon's coinage, generalizing one subtype of
[dixon-1994]'s split-ergative-on-TAM-lines pattern.

### Morpheme order and word-class status

Per [vazquez-alvarez-2011] §3.4: in Chol "the aspect
markers are auxiliaries" — `tyi` (perfective) and `mi` (imperfective)
are **aspectual auxiliaries** (independent words preceding the verbal
complex), not particles, not clitics, not verbal prefixes. Set A
ergative/genitive markers are prefixes on the verbal complex (per
[vazquez-alvarez-2011] §4.1.1; some prior literature treats them
as proclitics — [martinez-cruz-2007], [arcos-lopez-2009]).
Set B absolutive markers are suffixes (per [kaufman-norman-1984]
p. 90, originally cliticized pronouns).

Schematic order: `[Aux] [ERG-modifier*-ROOT-DERIV-STATUS-ABS]`, with
the bracketed verbal complex as a single phonological unit. Contrasts
with Kaqchikel's `[Aux] [ABS-ERG-Stem]` (high-ABS).

### The two agreement paradigms (Set A / Set B)

- **Set A** (ergative in perfective; nominative-or-genitive in
  non-perfective; possessive on nominals): prefixes
- **Set B** (absolutive in perfective; accusative in non-perfective):
  suffixes

### Case licensing (analytical, per [coon-2013])

- **ERG**: inherent from transitive *v*
- **ABS** (transitive): structural from Voice (low absolutive)
- **ABS** (intransitive): structural from Infl
- **GEN** (non-perfective S/A): from D under nominalization

### Accusative side (non-perfective)

In non-perfective aspect, the aspectual predicate *choñkol* embeds a
nominalized clause. The RON does NOT hold: the external argument may be
generated inside the nominalized clause. Result (Coon analysis):
S/A = GEN (from D), O = ABS (from Voice).

### What this fragment doesn't model

Per [vazquez-alvarez-2011] §1.9.4, Chol exhibits all
four Dixon alignment types: ergative-absolutive, nominative-accusative, **Split-S**
(some intransitives obligatorily Sa = Set A on light verb *cha'l*; others
obligatorily So = Set B), and **Fluid-S** (verbs like *wäy* 'sleep' that
take either Set A or Set B). The current `ArgPosition.intranS` collapses
Sa/So/fluid-S into a single intransitive subject category — sufficient
for the perfective↔non-perfective split formalization but undermodels
the agentive split. Future refinement: split into `intranSAgentive` /
`intranSPatientive` / `intranSFluid`.
-/

open Extraction (ExtractionTarget ExtractionMarkingStrategy)

namespace Chol

open Mayan (ExponentTable)

/-! ### Argument positions -/

/-- Argument positions in a Chol clause, aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T). -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Perfective (ergative) case assignment: `Mayan.ergCaseChol`
    (A → ERG, S/P → ABS). -/
abbrev ArgPosition.case : ArgPosition → Case := Mayan.ergCaseChol

/-- Non-perfective (extended-ergative) case assignment: `Mayan.accCaseChol`
    (S/A → GEN, P → ABS), shared with Q'anjob'al. -/
abbrev ArgPosition.accCase : ArgPosition → Case := Mayan.accCaseChol

/-! ### Absolutive position (LOW-ABS) -/

/-- Chol's absolutive morphemes appear in low (post-stem) position, from
    the morpheme order ASP-ERG-ROOT-(DERIV)-SUFFIX-ABS. -/
def absPosition : Mayan.ABSPosition := .low

/-! ### Extraction marking -/

namespace Extraction

/-- Chol requires **no Agent Focus morphology** for any extraction —
    unlike Q'anjob'al, the diagnostic for "lacking syntactic ergativity"
    in the [coon-mateo-pedro-preminger-2014] sense. Every argument
    extracts freely; the resulting ambiguity when both arguments are
    3rd person follows from the absent AF marking:
    `Maxki₁ tyi y-il-ä (___₁) jiñi wiñik (___₁)?`
    'Who saw the man?' / 'Who did the man see?' -/
def realize : ExtractionTarget → List (Features.Reflex Empty) :=
  fun _ => []

/-- WALS-style label: extraction is unmarked. -/
def strategy : ExtractionMarkingStrategy := .unmarked

end Extraction

/-! ### Non-finite absolutive availability -/

/-- In Chol non-finite (aspectless) embedded clauses, absolutive objects
    are available — Chol is LOW-ABS, so v⁰ licenses the object without Infl⁰.

    `Mejl [i-k'el-oñ]` 'She can see me.' (ABS object ✓)
    `Choñkol [k-mek'-ety]` 'I am hugging you.' (ABS object ✓) -/
def absObjectInNonFinite : Bool := true

/-- Absolutive intransitive subjects are not available in Chol non-finite
    clauses — they take the ergative/possessive prefix instead.

    `Choñkol [k-ts'äm-el]` 'I am bathing.' (ERG prefix, not ABS)
    `*Choñkol [ts'äm-i-yoñ]` intended: 'I am bathing.' (ABS ✗) -/
def absIntranSInNonFinite : Bool := false

/-! ### Person-number paradigm ([vazquez-alvarez-2011] Tables 9-10) -/

/-- Set A (ergative/possessive/genitive) markers by following-segment
    environment ([vazquez-alvarez-2011] Table 10, p. 83). 1sg `k-` is
    identical in both environments; 2sg surfaces pre-vocalically as
    `aw-`, 3sg as `iy-` (with speaker-variable omission of the initial
    vowel, i.e. a variant `y-` — [vazquez-alvarez-2011] examples
    (12)-(13) p. 76-77). Note the morphophonemic rule k- → j- /_k (1sg
    before a /k/ root, e.g., `tyi j-kajpelo` 'in my coffee field'
    p. 76). Plural cells are discontinuous: person prefix plus the
    inclusive enclitic `=la` for 1pl/2pl (the unmarked plural form per
    VA §4.2; the exclusive paradigm with `=l(oj)oñ` is a per-language
    refinement not exposed by the canonical φ-cell substrate) and the
    suffix `-ob` for 3pl. -/
def setAExponent : Morphology.Following → ExponentTable
  | .consonant =>
    [(.pn .first .Sing, [.pref "k"]), (.pn .second .Sing, [.pref "a"]),
     (.pn .third .Sing, [.pref "i"]),
     (.pn .first .Plur, [.pref "k", .encl "la"]),
     (.pn .second .Plur, [.pref "a", .encl "la"]),
     (.pn .third .Plur, [.pref "i", .suff "ob"])]
  | .vowel =>
    [(.pn .first .Sing, [.pref "k"]), (.pn .second .Sing, [.pref "aw"]),
     (.pn .third .Sing, [.pref "iy"]),
     (.pn .first .Plur, [.pref "k", .encl "la"]),
     (.pn .second .Plur, [.pref "aw", .encl "la"]),
     (.pn .third .Plur, [.pref "iy", .suff "ob"])]

/-- Set B (absolutive) markers: suffixes ([vazquez-alvarez-2011]
    Table 10, p. 83). 3rd singular has zero exponence; 3pl is the plural
    suffix alone; 1pl/2pl are discontinuous with the inclusive `=la`
    enclitic per the convention above. -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, [.suff "oñ"]), (.pn .second .Sing, [.suff "ety"]),
   (.pn .third .Sing, []),
   (.pn .first .Plur, [.suff "oñ", .encl "la"]),
   (.pn .second .Plur, [.suff "ety", .encl "la"]),
   (.pn .third .Plur, [.suff "ob"])]

/-- 3rd person absolutive is null — invariant across the standard
    Mayan branches (Cholan, Q'anjob'alan, Tseltalan, K'ichean) per
    [kaufman-norman-1984] Table 8 reconstruction. **Not** universally
    pan-Mayan: Mam's default Set B `tz'=` surfaces in the 3sg slot
    ([scott-2023]), and `Mayan.isStandard` excludes Mam from the
    cross-Mayan theorem
    (`CoonMateoPedroPreminger2014.mayan_p3sg_abs_null`). -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .Sing) = some [] := rfl

/-- 3rd person Set A allomorphy: pre-consonantal `i-` vs pre-vocalic
    `iy-`. Distinct from Q'anjob'al's `s-` vs `y-` (the proto-Mayan
    `*s-` ~ `*y-` allomorphy was leveled to `*r` → `y` in proto-Tseltalan,
    and Chol inherited the leveled form per [kaufman-norman-1984]
    p. 91). -/
theorem p3sg_erg_allomorphy :
    (setAExponent .consonant).realize (.pn .third .Sing) = some [.pref "i"] ∧
    (setAExponent .vowel).realize (.pn .third .Sing) = some [.pref "iy"] :=
  ⟨rfl, rfl⟩

end Chol
