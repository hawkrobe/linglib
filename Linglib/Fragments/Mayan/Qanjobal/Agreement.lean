module

public import Linglib.Syntax.Case.Basic
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Clause.ArgumentRole

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

@[expose] public section

namespace Qanjobal

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The Q'anjob'al verbal complex has the aspect marker, Set B and Set A before the stem and the
status suffix after it ([mateo-toledo-2008]). -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setB, .setA], [.status]⟩

/-- Q'anjob'al is ergative in every clause with a preverbal aspect marker, the imperfective
*chi-* included, and puts Set A on every subject in clauses without one, of which the
progressive with *lanan* is the one an aspect category names ([mateo-toledo-2008],
[imanishi-2020]); the other aspectless contexts, purpose clauses and aspectless complements
among them, lie outside the aspect vocabulary. -/
def assignCase : UD.Aspect → ArgumentRole → Case
  | .Prog => Alignment.extendedErgative
  | .Perf | .Imp | .Prosp | .Hab | .Iter => Alignment.ergative

/-! ### Person-number paradigm -/

/-- Set A (ergative/possessive) markers by following-segment
    environment ([coon-mateo-pedro-preminger-2014] table (13)). The 3pl
    cells are discontinuous exponents: person prefix plus the free
    plural word *heb'*. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.personNumber .first .singular, [.pref "hin"]),
     (.personNumber .second .singular, [.pref "ha"]),
     (.personNumber .third .singular, [.pref "s"]), (.personNumber .first .plural, [.pref "ko"]),
     (.personNumber .second .plural, [.pref "he"]),
     (.personNumber .third .plural, [.pref "s", .free "heb'"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "w"]), (.personNumber .second .singular, [.pref "h"]),
     (.personNumber .third .singular, [.pref "y"]), (.personNumber .first .plural, [.pref "j"]),
     (.personNumber .second .plural, [.pref "hey"]),
     (.personNumber .third .plural, [.pref "y", .free "heb'"])]

/-- The Set B (absolutive) markers are suffixes ([coon-mateo-pedro-preminger-2014] table (13)). The
3pl cell is the free plural word *heb'* alone (zero person exponence plus the plural particle); 1pl
*-on* is the table's ASCII for *-on̈* [-oŋ]. -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.suff "in"]), (.personNumber .second .singular, [.suff "ach"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.suff "on"]),
   (.personNumber .second .plural, [.suff "ex"]), (.personNumber .third .plural, [.free "heb'"])]

/-- 3rd person absolutive has zero exponence. -/
theorem p3sg_abs_null : setBExponent.realize (.personNumber .third .singular) = some [] := rfl

/-- 3rd person ergative is *s-* pre-consonantally, *y-* pre-vocalically. -/
theorem p3sg_erg_allomorphy :
    (setAExponent .consonant).realize (.personNumber .third .singular) = some [.pref "s"] ∧
    (setAExponent .vowel).realize (.personNumber .third .singular) = some [.pref "y"] := ⟨rfl, rfl⟩

end Qanjobal
