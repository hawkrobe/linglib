import Linglib.Typology.Plurals

/-!
# Tagalog plurality profile (WALS Chs 33–36)
@cite{wals-2013} @cite{himmelmann-2005-tagalog} @cite{schachter-otanes-1972}

The four WALS values committed below match the WALS v2020.4 entry for
Tagalog (`tgl`).

## Coding (Ch 33): plural word *mga*

WALS Ch 33 codes Tagalog as "plural word." @cite{schachter-otanes-1972}
§3.9 (p. 111) calls *mga* (phonemic /maŋah/, orthographic per
@cite{himmelmann-2005-tagalog} p. 353) a **PROCLITIC** — not an article,
not a free word. It has two readings: plural ('the children') and
approximative with cardinals ('about ten'). @cite{kroeger-1991-thesis}
(p. 14 ex. 12) treats it as enclitic on the preceding case marker
(*ang=mga=bata?* `NOM=PL=child`), without arguing the analysis.

Distribution restrictions (@cite{schachter-otanes-1972} p. 112): *mga*
does NOT occur with cardinal numbers (*sampung anak* 'ten children', not
\\**sampung mga anak*; *mga sampu* yields the approximative reading
'about ten'); does NOT occur after the personal-noun markers *si/ni/kay*;
and is non-obligatory throughout — "the pluralization of a noun need not
— and, in some cases in fact, cannot — be formally signaled if the
context makes the plural meaning clear" (p. 111).

## Associative plural (Ch 36): *sina*, NOT *mga*

The associative plural ("X and associates") is *sina X*, *not* *mga X*.
The personal-name marker paradigm *si/ni/kay* (sg) ↔ *sina/nina/kina* (pl)
is given as a single table by @cite{schachter-otanes-1972} §3.9 (p. 113);
S&O analyse the plurals as **derived by suffixation of *-na*** (with a
vowel change for *kay → kina*), not as a suppletive paradigm.
@cite{kroeger-1991-thesis} (p. 14 ex. 12) and @cite{himmelmann-2005-tagalog}
(Table 12.2, p. 358) tabulate only the singular set; the plural set
surfaces in Kroeger's glosses (p. 25 ex. 7 *sina=Ben* 'Ben and the
others'; p. 124 ex. 33) but is not analytically discussed.

@cite{schachter-otanes-1972} (p. 113) draws the *mga* / *sina* contrast
explicitly: "*mga* construction is used to designate two or more people
with the same name, while the plural-marker construction is used to
designate the person named plus other people. Thus *ang mga Santos* is
'the Santoses', while *sina Santos* is 'Santos and others (who may or
may not also be named Santos)'."

## Pronoun plurality (Ch 35) and clusivity gap

The substrate's `.personNumberStem` value matches WALS Ch 35 but
underdetermines Tagalog's actual paradigm: *kitá* (1+2 minimal-inclusive,
the "we two" form), *tayo* (1+2+3 augmented-inclusive), and *kami* (1+3
exclusive) instantiate Cysouw's *minimal-augmented* type (see
`Fragments.Tagalog.clusivitySystem` in `Fragments/Tagalog/Pronouns.lean`).
The full Table 12.2 paradigm from @cite{himmelmann-2005-tagalog} is also
documented there.
-/

namespace Fragments.Tagalog

/-- Tagalog plurality profile across @cite{wals-2013} Chs 33-36.

Coding (Ch 33): plural word *mga*. Occurrence (Ch 34): all nouns, always
optional. Pronoun plurality (Ch 35): person-number stem (refined to
minimal-augmented in `Fragments.Tagalog.clusivitySystem`). Associative
(Ch 36): unique periphrastic — *sina* on personal names. -/
def pluralityProfile : Typology.PluralityProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , coding := .pluralWord
  , occurrence := .allNounsAlwaysOptional
  , pronounPlurality := .personNumberStem
  , associativePlural := .uniquePeriphrastic }

end Fragments.Tagalog
