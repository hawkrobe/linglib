import Linglib.Typology.Pronouns
import Linglib.Features.Clusivity

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
an augmented *tayo* (1+2+3); the exclusive *kami* remains a single
category. This is a finer typological cut than WALS Ch 39's binary
incl/excl coding can express, which is why the WALS-shaped
`inclusiveExclusive` field below underdetermines the paradigm.

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
def pronounProfile : Typology.PronounProfile :=
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
def pronounShapeProfile : Typology.PronounShapeProfile :=
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

end Fragments.Tagalog
