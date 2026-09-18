import Linglib.Syntax.Case.Basic
import Linglib.Phonology.Segmental.Defs
import Linglib.Fragments.Mayan.Agreement
import Linglib.Syntax.Clause.ArgumentRole

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
* `Qanjobal.template`, `Qanjobal.assignCase`: the verbal complex, with Set B
  between the aspect marker and the stem, and case ergative wherever an aspect
  marker is present and extended-ergative in the progressive.

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
put Set A on all subjects. The choice of genitive rather than nominative for Set A
on non-perfective subjects is `Alignment.extendedErgative`'s, following
[coon-2013]'s analysis; the descriptive grammars call the pattern
nominative-accusative.

One real Cholan/Q'anjob'alan difference the shared alignment substrate
does not capture is aspect-marker word class: Chol markers are
auxiliaries (independent words *tyi* perfective, *mi* imperfective;
[vazquez-alvarez-2011] §3.4), whereas Q'anjob'al markers are clitics or
"grammaticized particles" (*(ma)x-* completive, *chi/ch-* incompletive,
*(ho)q-* irrealis; [mateo-toledo-2008] §1.1.2, Kaufman 1990:71,
Robertson 1992:57). `Qanjobal.assignCase` captures the alignment
facts, not the morpheme-class difference.
-/

namespace Qanjobal

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The position classes of the Q'anjob'al verbal complex: the aspect marker, Set B and Set A
before the stem, the status suffix after it ([mateo-toledo-2008]). -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setB, .setA], [.status]⟩

/-- Q'anjob'al is ergative in every clause with a preverbal aspect marker, the imperfective
*chi-* included, and puts Set A on every subject in clauses without one, of which the
progressive with *lanan* is the one an aspect category names ([mateo-toledo-2008],
[imanishi-2020]); the other aspectless contexts, purpose clauses and aspectless complements
among them, lie outside the aspect vocabulary. -/
def assignCase : UD.Aspect → ArgumentRole → Case
  | .Prog => Alignment.extendedErgative.assignCase
  | .Perf | .Imp | .Prosp | .Hab | .Iter => Alignment.ergative.assignCase

/-! ### Person-number paradigm -/

/-- Set A (ergative/possessive) markers by following-segment
    environment ([coon-mateo-pedro-preminger-2014] table (13)). The 3pl
    cells are discontinuous exponents: person prefix plus the free
    plural word *heb'*. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.pn .first .singular, [.pref "hin"]), (.pn .second .singular, [.pref "ha"]),
     (.pn .third .singular, [.pref "s"]), (.pn .first .plural, [.pref "ko"]),
     (.pn .second .plural, [.pref "he"]),
     (.pn .third .plural, [.pref "s", .free "heb'"])]
  | .vowel =>
    [(.pn .first .singular, [.pref "w"]), (.pn .second .singular, [.pref "h"]),
     (.pn .third .singular, [.pref "y"]), (.pn .first .plural, [.pref "j"]),
     (.pn .second .plural, [.pref "hey"]),
     (.pn .third .plural, [.pref "y", .free "heb'"])]

/-- Set B (absolutive) markers: suffixes
    ([coon-mateo-pedro-preminger-2014] table (13)). The 3pl cell is the
    free plural word *heb'* alone (zero person exponence plus the
    plural particle); 1pl *-on* is the table's ASCII for *-on̈* [-oŋ]. -/
def setBExponent : ExponentTable :=
  [(.pn .first .singular, [.suff "in"]), (.pn .second .singular, [.suff "ach"]),
   (.pn .third .singular, []), (.pn .first .plural, [.suff "on"]),
   (.pn .second .plural, [.suff "ex"]), (.pn .third .plural, [.free "heb'"])]

/-- 3rd person absolutive has zero exponence. -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .singular) = some [] := rfl

/-- 3rd person ergative is *s-* pre-consonantally, *y-* pre-vocalically. -/
theorem p3sg_erg_allomorphy :
    (setAExponent .consonant).realize (.pn .third .singular) = some [.pref "s"] ∧
    (setAExponent .vowel).realize (.pn .third .singular) = some [.pref "y"] := ⟨rfl, rfl⟩

end Qanjobal
