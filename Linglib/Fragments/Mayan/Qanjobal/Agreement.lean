import Linglib.Features.Case.Basic
import Linglib.Fragments.Mayan.Params

/-!
# Q'anjob'al Agreement and Case Fragment

Agreement morphology and case assignment for Q'anjob'al (Q'anjob'alan,
Mayan), following [mateo-toledo-2008] and [imanishi-2020]: a high
absolutive VSO language whose split ergativity is triggered by the
absence of a preverbal aspect marker. Q'anjob'al has the same Set A
(ergative) / Set B (absolutive) paradigm as other Mayan languages. Per
[mateo-toledo-2008] p. 9 it sits in the "Q'anjob'alan group,
Q'anjob'alan branch, Western division" of the Mayan family (citing
England 1992:21, Kaufman 1974) — alongside the Cholan-Tzeltalan branch
(where Chol lives) within Western Mayan.

## Main declarations

* `Qanjobal.setAExponentPreC`, `Qanjobal.setAExponentPreV`,
  `Qanjobal.setBExponent`: Set A pre-consonantal and pre-vocalic
  ergative allomorphs and the Set B absolutive suffixes
  ([coon-mateo-pedro-preminger-2014] table (13)).
* `Qanjobal.ArgPosition` with `.case`, `.accCase`: argument positions
  and their canonical-ergative and split (extended-ergative) case,
  shared with Chol via `Mayan.ergCaseQanjobalan` /
  `Mayan.accCaseQanjobalan`.
* `Qanjobal.absPosition`: HIGH-ABS morpheme placement.

## Implementation notes

Per [mateo-toledo-2008] §1.3, ex. (35), the verbal predicate structure
is `Asp + (Particle) + Abs + (Particle) + Erg-Verb + (Particle) +
(DIRs)`, i.e. `[Asp] [Abs Erg-Verb]` — the high absolutive template,
against Chol's low-absolutive `[Aux] [Erg-Verb-Abs]`
([vazquez-alvarez-2011] §3.4).

Unlike Chol's aspect-category split (accusative in all non-perfective
aspects), Q'anjob'al splits only in clauses lacking an overt preverbal
aspect marker — "split ergativity occurs in any clause without an
overt preverbal aspect marker" ([mateo-toledo-2008] §1.1.1, citing
Mateo 2004a/2007b) — so the imperfective `chi-` keeps canonical
ergative, and only aspectless contexts (e.g. the `lanan` progressive)
put Set A on all subjects. The three-branch split survey and the
`.gen`-vs-`.nom` discussion live in `Fragments/Mayan/Params.lean`,
whose `Mayan.caseQanjobalan` this file consumes.

One real Cholan/Q'anjob'alan difference the shared alignment substrate
does not capture is aspect-marker word class: Chol markers are
auxiliaries (independent words *tyi* perfective, *mi* imperfective;
[vazquez-alvarez-2011] §3.4), whereas Q'anjob'al markers are clitics or
"grammaticized particles" (*(ma)x-* completive, *chi/ch-* incompletive,
*(ho)q-* irrealis; [mateo-toledo-2008] §1.1.2, Kaufman 1990:71,
Robertson 1992:57). `Mayan.caseQanjobalan` captures the alignment
facts, not the morpheme-class difference.
-/

namespace Qanjobal

open Mayan (ExponentTable)

/-! ### Argument positions -/

/-- Argument positions, aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T). -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Canonical ergative case assignment (clauses with an overt preverbal
    aspect marker), shared with Chol via `Mayan.ergCaseQanjobalan`
    (= `Alignment.ergative.assignCase`). -/
abbrev ArgPosition.case : ArgPosition → Case := Mayan.ergCaseQanjobalan

/-- Split (extended-ergative) case assignment in aspectless contexts,
    via the `.Prog` projection `Mayan.accCaseQanjobalan`
    (= `Alignment.extendedErgative.assignCase`) — making the
    accusative-side parallel with Chol true by construction. -/
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
    ([coon-mateo-pedro-preminger-2014] table (13)). The 3pl cell *heb'*
    is an independent plural word (null person exponent plus the plural
    particle), quoted as in the source table; 1pl *-on* is the table's
    ASCII for *-on̈* [-oŋ]. -/
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
