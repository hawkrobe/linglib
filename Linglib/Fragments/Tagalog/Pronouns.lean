import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Pronoun.WALS
import Linglib.Features.Clusivity
import Linglib.Features.Person.Decomposition

/-!
# Tagalog pronoun profile (WALS Chs 39, 40, 44–48)
[wals-2013] [himmelmann-2005-tagalog]

## Pronoun paradigm (Himmelmann 2005 Table 12.2, p. 358)

```
                ANG-FORM      NG-FORM       SA-FORM
1.SG            akó           ko            akin
2.SG            ikáw / ka     mo            iyo / iyó
3.SG            siyá          niyá          kaniyá
1.DU.IN         kitá / katá   nitá          kanitá
1.PL.IN         tayo          natin         atin
1.PL.EX         kamí          namin         amin
2.PL            kayó          ninyó         inyó
3.PL            silá          nilá          kanilá
```

[himmelmann-2005-tagalog] labels the columns SPEC / POSS(GEN) /
LOC(DAT) (p. 358; the *sa*-form of personal pronouns and personal names
is glossed DAT rather than LOC because of distributional differences).
[kroeger-1991-thesis] (p. 14, ex. 12) uses the cleaner labels
NOMINATIVE / GENITIVE / DATIVE, explicitly rejecting the older
"topic"/"complement" terminology.

## Clusivity (system-level)

Tagalog instantiates Cysouw's *minimal-augmented* type ([cysouw-2009]):
the inclusive splits into a minimal 1du.in form (1+2 only, "we two") and
an augmented *tayo* (1+2+others — speaker + addressee + additional
referents, of any number; [schachter-otanes-1972] p. 89 glosses it
as "you (singular) and I (and others)" / "you (plural) and I"); the
exclusive *kami* remains a single category. This is a finer typological
cut than WALS Ch 39's binary incl/excl coding can express, which is why
the WALS-derived `Pronoun.inclusiveExclusive "tgl"` underdetermines the
paradigm.

The *kitá* / *katá* cell warrants care. [schachter-otanes-1972]
Chart 7 (p. 88) tabulates the 1du.in NOM as ***kata*** (with *nita*/*kanita*
GEN/DAT) — and adds a separate portmanteau ***kita*** (p. 89) that combines
1sg.GEN with 2sg.NOM (occurring "in place of the non-occurring sequences
\\**ko ka* and \\**ka ko*", e.g. in 'I [verb] you' constructions).
[himmelmann-2005-tagalog]'s Table 12.2 lists *kitá / katá* together
as the 1.DU.IN ang-form, conflating these. S&O (p. 89) further note that
"the dual non-plural pronouns are obsolescent in educated Manila Tagalog,
and many speakers do not use them at all, using the dual plural
*tayo/natin/atin* for 'you (singular) and I' as well as 'you (plural) and
I'." The minimal-augmented classification therefore reflects the
historical/textbook system; modern colloquial Manila Tagalog effectively
collapses to plain inclExcl.
-/

namespace Tagalog

/-- Tagalog clusivity system per [cysouw-2009]: minimal-augmented,
    with the historical 1-dual-inclusive *kata*
    ([schachter-otanes-1972] p. 88) alongside the augmented-inclusive
    *tayo* and the exclusive *kami*. Modern Manila Tagalog has largely
    lost the dual; this field reflects the textbook paradigm, not
    colloquial usage. Refines the binary WALS Ch 39 value
    `Pronoun.inclusiveExclusive "tgl"` (derived from `Data.WALS`). -/
def clusivitySystem : Features.Clusivity.System := .minimalAugmented

-- ============================================================================
-- Pronoun paradigm (person + number + clusivity, three case series)
-- ============================================================================

/-! The independent-pronoun paradigm per [schachter-otanes-1972] Chart 7
    (p. 88): each cell is a `PersonalPronoun` carrying person, number, and
    clusivity, in three case series — *ang* (NOM), *ng* (GEN), *sa* (DAT). The
    [cysouw-2009] `category` is *derived* from those features
    (`Pronoun.category`), not stored. The minimal-augmented split is the dual
    inclusive *kata* (1+2) vs the plural inclusive *tayo* (1+2+others), with the
    exclusive *kami* (1+others). The *kitá* form [himmelmann-2005-tagalog]
    Table 12.2 lists alongside *katá* is a separate 1sg.GEN+2sg.NOM portmanteau
    ([schachter-otanes-1972] p. 89), not a 1du.in pronoun. -/

open Person (Category)

-- 1st singular
def ako    : PersonalPronoun := { form := "ako",    person := some .first,  number := some .singular, case_ := some .nom }
def ko     : PersonalPronoun := { form := "ko",     person := some .first,  number := some .singular, case_ := some .gen }
def akin   : PersonalPronoun := { form := "akin",   person := some .first,  number := some .singular, case_ := some .dat }
-- 2nd singular
def ikaw   : PersonalPronoun := { form := "ikaw",   person := some .second, number := some .singular, case_ := some .nom }
def mo     : PersonalPronoun := { form := "mo",     person := some .second, number := some .singular, case_ := some .gen }
def iyo    : PersonalPronoun := { form := "iyo",    person := some .second, number := some .singular, case_ := some .dat }
-- 3rd singular
def siya   : PersonalPronoun := { form := "siya",   person := some .third,  number := some .singular, case_ := some .nom }
def niya   : PersonalPronoun := { form := "niya",   person := some .third,  number := some .singular, case_ := some .gen }
def kaniya : PersonalPronoun := { form := "kaniya", person := some .third,  number := some .singular, case_ := some .dat }
-- 1st dual inclusive (minimal inclusive): *kata*
def kata   : PersonalPronoun := { form := "kata",   person := some .firstInclusive,  number := some .dual, case_ := some .nom }
def nita   : PersonalPronoun := { form := "nita",   person := some .firstInclusive,  number := some .dual, case_ := some .gen }
def kanita : PersonalPronoun := { form := "kanita", person := some .firstInclusive,  number := some .dual, case_ := some .dat }
-- 1st plural inclusive (augmented inclusive): *tayo*
def tayo   : PersonalPronoun := { form := "tayo",   person := some .firstInclusive,  number := some .plural, case_ := some .nom }
def natin  : PersonalPronoun := { form := "natin",  person := some .firstInclusive,  number := some .plural, case_ := some .gen }
def atin   : PersonalPronoun := { form := "atin",   person := some .firstInclusive,  number := some .plural, case_ := some .dat }
-- 1st plural exclusive: *kami*
def kami   : PersonalPronoun := { form := "kami",   person := some .firstExclusive,  number := some .plural, case_ := some .nom }
def namin  : PersonalPronoun := { form := "namin",  person := some .firstExclusive,  number := some .plural, case_ := some .gen }
def amin   : PersonalPronoun := { form := "amin",   person := some .firstExclusive,  number := some .plural, case_ := some .dat }
-- 2nd plural
def kayo   : PersonalPronoun := { form := "kayo",   person := some .second, number := some .plural, case_ := some .nom }
def ninyo  : PersonalPronoun := { form := "ninyo",  person := some .second, number := some .plural, case_ := some .gen }
def inyo   : PersonalPronoun := { form := "inyo",   person := some .second, number := some .plural, case_ := some .dat }
-- 3rd plural
def sila   : PersonalPronoun := { form := "sila",   person := some .third,  number := some .plural, case_ := some .nom }
def nila   : PersonalPronoun := { form := "nila",   person := some .third,  number := some .plural, case_ := some .gen }
def kanila : PersonalPronoun := { form := "kanila", person := some .third,  number := some .plural, case_ := some .dat }

/-- The Tagalog independent-pronoun inventory (all three case series). -/
def pronouns : List PersonalPronoun :=
  [ako, ko, akin, ikaw, mo, iyo, siya, niya, kaniya,
   kata, nita, kanita, tayo, natin, atin, kami, namin, amin,
   kayo, ninyo, inyo, sila, nila, kanila]

/-- The *ang* (nominative) series, one form per [cysouw-2009] category in
    canonical order. -/
def angSeries : List PersonalPronoun := [ako, ikaw, siya, kata, tayo, kami, kayo, sila]

/-- The *ang* series realizes exactly [cysouw-2009]'s eight person
    categories — *derived* from each form's person + number + clusivity, not
    stored as a tag. -/
theorem angSeries_categories_match :
    angSeries.map (·.category) = Category.all.map some := by decide

/-- Tagalog marks inclusive/exclusive in the first-person plural: *tayo* is
    inclusive, *kami* exclusive — read off the object's `clusivity` field. -/
theorem incl_excl_distinct :
    tayo.person = some .firstInclusive ∧ kami.person = some .firstExclusive := ⟨rfl, rfl⟩

/-- The minimal-augmented property: a dual inclusive *kata* (1+2) alongside the
    plural inclusive *tayo* — what makes Tagalog minimal-augmented rather than
    plain inclusive/exclusive ([cysouw-2009]). -/
theorem minimal_augmented :
    kata.number = some .dual ∧ kata.person = some .firstInclusive ∧
    tayo.number = some .plural ∧ tayo.person = some .firstInclusive := ⟨rfl, rfl, rfl, rfl⟩

/-- Cross-substrate consistency: the inventory contains a minimal-inclusive
    (dual inclusive) form iff the language commits to the minimal-augmented
    clusivity system. -/
theorem clusivity_system_consistent :
    pronouns.any (fun p => decide (p.category = some .minIncl)) =
      clusivitySystem.hasMinimalAugmented := by decide

/-- Every Tagalog pronoun is well-formed: clusivity is borne only by the
    first-person dual/plural forms (`Pronoun.WellFormed`). -/
theorem all_wellFormed : pronouns.all (fun p => decide p.WellFormed) = true := by decide

/-- WALS Ch 39's coding of Tagalog agrees with the image of its Cysouw
    clusivity system under `fromClusivity`. The WALS value is derived from the
    `Data.WALS` layer by ISO (no hand-stipulation), so this catches drift
    between WALS and the clusivity commitment. -/
theorem wals_clusivity_consistent :
    Pronoun.inclusiveExclusive "tgl" =
      some (Pronoun.InclusiveExclusive.fromClusivity clusivitySystem) := by decide

end Tagalog
