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

* `Qanjobal.setAExponent`, `Qanjobal.setBExponent`: Set A ergative
  markers by following-segment environment (pre-consonantal vs
  pre-vocalic variant shapes) and the Set B absolutive suffixes
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

/-- Set A (ergative/possessive) markers by following-segment
    environment ([coon-mateo-pedro-preminger-2014] table (13)). The 3pl
    cells are discontinuous exponents: person prefix plus the free
    plural word *heb'*. -/
def setAExponent : Morphology.Following → ExponentTable
  | .consonant =>
    [(.pn .first .Sing, [.pref "hin"]), (.pn .second .Sing, [.pref "ha"]),
     (.pn .third .Sing, [.pref "s"]), (.pn .first .Plur, [.pref "ko"]),
     (.pn .second .Plur, [.pref "he"]),
     (.pn .third .Plur, [.pref "s", .free "heb'"])]
  | .vowel =>
    [(.pn .first .Sing, [.pref "w"]), (.pn .second .Sing, [.pref "h"]),
     (.pn .third .Sing, [.pref "y"]), (.pn .first .Plur, [.pref "j"]),
     (.pn .second .Plur, [.pref "hey"]),
     (.pn .third .Plur, [.pref "y", .free "heb'"])]

/-- Set B (absolutive) markers: suffixes
    ([coon-mateo-pedro-preminger-2014] table (13)). The 3pl cell is the
    free plural word *heb'* alone (zero person exponence plus the
    plural particle); 1pl *-on* is the table's ASCII for *-on̈* [-oŋ]. -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, [.suff "in"]), (.pn .second .Sing, [.suff "ach"]),
   (.pn .third .Sing, []), (.pn .first .Plur, [.suff "on"]),
   (.pn .second .Plur, [.suff "ex"]), (.pn .third .Plur, [.free "heb'"])]

/-- 3rd person absolutive has zero exponence. -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .Sing) = some [] := rfl

/-- 3rd person ergative is *s-* pre-consonantally, *y-* pre-vocalically. -/
theorem p3sg_erg_allomorphy :
    (setAExponent .consonant).realize (.pn .third .Sing) = some [.pref "s"] ∧
    (setAExponent .vowel).realize (.pn .third .Sing) = some [.pref "y"] := ⟨rfl, rfl⟩

end Qanjobal
