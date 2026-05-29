import Linglib.Typology.Pronoun.Basic
import Linglib.Features.Clusivity
import Linglib.Features.Person

/-!
# Tagalog pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013} @cite{himmelmann-2005-tagalog}

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

@cite{himmelmann-2005-tagalog} labels the columns SPEC / POSS(GEN) /
LOC(DAT) (p. 358; the *sa*-form of personal pronouns and personal names
is glossed DAT rather than LOC because of distributional differences).
@cite{kroeger-1991-thesis} (p. 14, ex. 12) uses the cleaner labels
NOMINATIVE / GENITIVE / DATIVE, explicitly rejecting the older
"topic"/"complement" terminology.

## Clusivity (system-level)

Tagalog instantiates Cysouw's *minimal-augmented* type (@cite{cysouw-2009}):
the inclusive splits into a minimal 1du.in form (1+2 only, "we two") and
an augmented *tayo* (1+2+others — speaker + addressee + additional
referents, of any number; @cite{schachter-otanes-1972} p. 89 glosses it
as "you (singular) and I (and others)" / "you (plural) and I"); the
exclusive *kami* remains a single category. This is a finer typological
cut than WALS Ch 39's binary incl/excl coding can express, which is why
the WALS-shaped `inclusiveExclusive` field below underdetermines the
paradigm.

The *kitá* / *katá* cell warrants care. @cite{schachter-otanes-1972}
Chart 7 (p. 88) tabulates the 1du.in NOM as ***kata*** (with *nita*/*kanita*
GEN/DAT) — and adds a separate portmanteau ***kita*** (p. 89) that combines
1sg.GEN with 2sg.NOM (occurring "in place of the non-occurring sequences
\\**ko ka* and \\**ka ko*", e.g. in 'I [verb] you' constructions).
@cite{himmelmann-2005-tagalog}'s Table 12.2 lists *kitá / katá* together
as the 1.DU.IN ang-form, conflating these. S&O (p. 89) further note that
"the dual non-plural pronouns are obsolescent in educated Manila Tagalog,
and many speakers do not use them at all, using the dual plural
*tayo/natin/atin* for 'you (singular) and I' as well as 'you (plural) and
I'." The minimal-augmented classification therefore reflects the
historical/textbook system; modern colloquial Manila Tagalog effectively
collapses to plain inclExcl.
-/

namespace Fragments.Tagalog

/-- Tagalog (Austronesian, Philippine). Inclusive/exclusive in
    independent pronouns (kami vs tayo); no person marking on verbs
    (WALS); no gender distinctions (siya is gender-neutral); multiple
    politeness distinctions (ikaw/kayo/po); existential construction
    for indefinite reference; intensifier (mismo) differentiated from
    reflexive (sarili); no adpositions per WALS Ch 48. -/
def pronounProfile : Pronoun.Profile :=
  { language := "Tagalog"
  , family := "Austronesian"
  , iso := "tgl"
  , inclusiveExclusive := some .inclusiveExclusive
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .multiple
  , indefiniteType := some .existentialConstruction
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noAdpositions }

/-- Tagalog pronoun phonological shape (WALS Chs 136–137): no M-T; no /m/
    in 1SG (*ako*); no N-M; /m/ present in 2SG (*mo*). -/
def pronounShapeProfile : Pronoun.ShapeProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , mtPronouns := some .absent
  , mIn1sg := some .absent
  , nmPronouns := some .absent
  , mIn2sg := some .present }

/-- Tagalog clusivity system per @cite{cysouw-2009}: minimal-augmented,
    with the historical 1-dual-inclusive *kata*
    (@cite{schachter-otanes-1972} p. 88) alongside the augmented-inclusive
    *tayo* and the exclusive *kami*. Modern Manila Tagalog has largely
    lost the dual; this field reflects the textbook paradigm, not
    colloquial usage. Refines the binary WALS Ch 39 value
    `pronounProfile.inclusiveExclusive = some .inclusiveExclusive`. -/
def clusivitySystem : Features.Clusivity.System := .minimalAugmented

-- ============================================================================
-- Pronoun paradigm (structured)
-- ============================================================================

/-- A row of the Tagalog pronoun paradigm: a Cysouw 2009 person/number
    category and its three case forms. -/
structure PronounRow where
  category : Features.Person.Category
  /-- *ang*-form (SPEC / NOM). -/
  angForm : String
  /-- *ng*-form (POSS / GEN). -/
  ngForm : String
  /-- *sa*-form (LOC / DAT). -/
  saForm : String
  deriving Repr

/-- The Tagalog independent-pronoun paradigm per @cite{schachter-otanes-1972}
    Chart 7 (p. 88), mapped onto Cysouw 2009 categories.

    The 1.DU.IN.NOM cell is *kata* per S&O Chart 7; the *kitá* form
    @cite{himmelmann-2005-tagalog} Table 12.2 lists alongside *katá* is
    in S&O p. 89 a separate portmanteau combining 1sg.GEN with 2sg.NOM
    (in 'I [verb] you' clauses), not a 1du.in pronoun. -/
def pronounParadigm : List PronounRow :=
  [ { category := .s1,        angForm := "ako",   ngForm := "ko",     saForm := "akin"   }
  , { category := .s2,        angForm := "ikaw",  ngForm := "mo",     saForm := "iyo"    }
  , { category := .s3,        angForm := "siya",  ngForm := "niya",   saForm := "kaniya" }
  , { category := .minIncl,   angForm := "kata",  ngForm := "nita",   saForm := "kanita" }
  , { category := .augIncl,   angForm := "tayo",  ngForm := "natin",  saForm := "atin"   }
  , { category := .excl,      angForm := "kami",  ngForm := "namin",  saForm := "amin"   }
  , { category := .secondGrp, angForm := "kayo",  ngForm := "ninyo",  saForm := "inyo"   }
  , { category := .thirdGrp,  angForm := "sila",  ngForm := "nila",   saForm := "kanila" }
  ]

/-- The categories enumerated by the paradigm are exactly Cysouw's
    canonical ordering (singulars first, then groups). Subsumes a
    `length = Category.all.length` claim. -/
theorem pronounParadigm_categories_match :
    pronounParadigm.map (·.category) = Features.Person.Category.all := rfl

/-- Cross-substrate consistency: the paradigm includes a minimal-inclusive
    row iff the language commits to the minimal-augmented clusivity
    system. The forward direction encodes the minimal-augmented type's
    definition (a separate "we two" form for speaker + addressee only);
    the converse here holds because Tagalog has both. -/
theorem clusivity_system_consistent_with_paradigm :
    (pronounParadigm.map (·.category)).contains .minIncl =
      clusivitySystem.hasMinimalAugmented := by decide

/-- The WALS Ch 39 image of Tagalog's Cysouw clusivity system agrees with
    the WALS-side commitment in `pronounProfile.inclusiveExclusive`. This
    catches drift if either commitment changes without the other. -/
theorem wals_clusivity_consistent :
    pronounProfile.inclusiveExclusive =
      some (Pronoun.InclusiveExclusive.fromClusivity clusivitySystem) := rfl

end Fragments.Tagalog
