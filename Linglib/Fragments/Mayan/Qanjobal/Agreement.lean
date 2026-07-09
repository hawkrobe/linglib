import Linglib.Features.Case.Basic
import Linglib.Fragments.Mayan.Params

/-!
# Q'anjob'al Agreement and Case Fragment

Agreement morphology and case assignment for Q'anjob'al (Q'anjob'alan,
Mayan), following [mateo-toledo-2008] and [imanishi-2020]: a high
absolutive VSO language with aspect-based split ergativity. Q'anjob'al
has the same Set A (ergative) / Set B (absolutive) paradigm as other
Mayan languages. Per [mateo-toledo-2008] p. 9 it sits in the
"Q'anjob'alan group, Q'anjob'alan branch, Western division" of the
Mayan family (citing England 1992:21, Kaufman 1974) — sister to the
Cholan-Tzeltalan branch (where Chol lives) within Western Mayan.

## Main declarations

* `Qanjobal.setAExponentPreC`, `Qanjobal.setAExponentPreV`,
  `Qanjobal.setBExponent`: Set A pre-consonantal and pre-vocalic
  ergative allomorphs and the Set B absolutive suffixes
  ([coon-mateo-pedro-preminger-2014] table (13)).
* `Qanjobal.ArgPosition` with `.case`, `.accCase`: argument positions
  and their perfective and non-perfective case, shared with Chol via
  `Mayan.ergCaseQanjobalan` / `Mayan.accCaseQanjobalan`.
* `Qanjobal.absPosition`: HIGH-ABS morpheme placement.

## Implementation notes

Per [mateo-toledo-2008] §1.3, ex. (35), the verbal predicate structure
is `Asp + (Particle) + Abs + (Particle) + Erg-Verb + (Particle) +
(DIRs)`, i.e. `[Asp] [Abs Erg-Verb]` — the high absolutive template,
against Chol's low-absolutive `[Aux] [Erg-Verb-Abs]`
([vazquez-alvarez-2011] §3.4).

One real Cholan/Q'anjob'alan difference the shared substrate
`caseExtErg` does not capture is aspect-marker word class: Chol markers
are auxiliaries (independent words *tyi* perfective, *mi* imperfective;
[vazquez-alvarez-2011] §3.4), whereas Q'anjob'al markers are clitics or
"grammaticized particles" (*(ma)x-* completive, *chi/ch-* incompletive,
*(ho)q-* irrealis; [mateo-toledo-2008] §1.1.2, Kaufman 1990:71,
Robertson 1992:57). The alignment behavior is nonetheless the same —
split ergativity in any clause without an overt preverbal aspect marker
([mateo-toledo-2008] §1.1.1, citing Mateo 2004a/2007b), attributed to
nominalization following Larsen & Norman 1979 — so `Mayan.caseExtErg`
captures the alignment convergence, not the morpheme-class convergence.

The non-perfective pattern has a descriptive and an analytical framing
(as in Chol). [mateo-toledo-2008] §1.1.1 (p. 50) describes it as a
"nominative-accusative system (Dixon 1994:104)" — Set A ergative
morphemes mark both transitive and intransitive subjects in aspectless
contexts — while the "extended ergative / Set A = GEN-from-D" framing
comes from formal-syntactic analyses (Coon 2013, Imanishi 2020) where
Set A is genitive licensed by D under nominalization. The substrate's
`extendedErgative.assignCase` returns `.gen` (the analytical view); a
descriptive-grammar implementation would return `.nom`.

The shared substrate works because both languages converge via
independent grammaticalization. [mateo-toledo-2008] fn. 3 (p. 50): "in
Q'anjob'alan languages, split ergativity is associated with the lack of
an aspect marker (that is likely to be driven by nominalization, see
Larsen and Norman 1979)" — the same mechanism Coon (2013) argues for
Chol. They are sister branches of Western Mayan with no
common-inheritance unit, which is why the substrate is named
`caseExtErg` (the typological convergence) rather than after one
language family.
-/

namespace Qanjobal

open Mayan (ExponentTable)
open Agreement

/-! ### Argument positions -/

/-- Argument positions, aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T). -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Perfective case assignment, shared with Chol via
    `Mayan.ergCaseQanjobalan` (= `Alignment.ergative.assignCase`). -/
abbrev ArgPosition.case : ArgPosition → Case := Mayan.ergCaseQanjobalan

/-- Non-perfective case assignment, shared with Chol via
    `Mayan.accCaseQanjobalan` (= `Alignment.extendedErgative.assignCase`) —
    making the accusative-side parallel true by construction. -/
abbrev ArgPosition.accCase : ArgPosition → Case := Mayan.accCaseQanjobalan

/-! ### Absolutive position (HIGH-ABS) -/

/-- HIGH-ABS: absolutive morphemes sit on the aspect marker (pre-stem),
    from the morpheme order ASP-ABS-ERG-ROOT-SUFFIX. -/
def absPosition : Mayan.ABSPosition := .high

/-! ### Person-number paradigm -/

/-- Set A (ergative/possessive) markers: pre-consonantal allomorphs
    ([coon-mateo-pedro-preminger-2014] table (13)). -/
def setAExponentPreC : ExponentTable :=
  [(.pn .first .Sing, "hin-"), (.pn .second .Sing, "ha-"), (.pn .third .Sing, "s-"),
   (.pn .first .Plur, "ko-"), (.pn .second .Plur, "he-"), (.pn .third .Plur, "s-…heb'")]

/-- Set A (ergative/possessive) markers: pre-vocalic allomorphs
    ([coon-mateo-pedro-preminger-2014] table (13)). -/
def setAExponentPreV : ExponentTable :=
  [(.pn .first .Sing, "w-"), (.pn .second .Sing, "h-"), (.pn .third .Sing, "y-"),
   (.pn .first .Plur, "j-"), (.pn .second .Plur, "hey-"), (.pn .third .Plur, "y-…heb'")]

/-- Canonical Set A exponent table for cross-Mayan typology. The
    pre-consonantal allomorph is the citation form; per-context
    realization uses `setAExponentPreV` before vowels. -/
abbrev setAExponent : ExponentTable := setAExponentPreC

/-- Set B (absolutive) markers: suffixes
    ([coon-mateo-pedro-preminger-2014] table (13)). -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, "-in"), (.pn .second .Sing, "-ach"), (.pn .third .Sing, "-∅"),
   (.pn .first .Plur, "-on"), (.pn .second .Plur, "-ex"), (.pn .third .Plur, "heb'")]

/-- 3rd person absolutive is null (∅). -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .Sing) = some "-∅" := rfl

/-- 3rd person ergative (pre-vocalic) is *y-*, pre-consonantal is *s-*. -/
theorem p3sg_erg_allomorphy :
    setAExponentPreC.realize (.pn .third .Sing) = some "s-" ∧
    setAExponentPreV.realize (.pn .third .Sing) = some "y-" := ⟨rfl, rfl⟩

end Qanjobal
