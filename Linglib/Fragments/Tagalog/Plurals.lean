/-!
# Tagalog plurality profile (WALS Chs 33–36)
[wals-2013] [himmelmann-2005-tagalog] [schachter-otanes-1972]

The four WALS values committed below match the WALS v2020.4 entry for
Tagalog (`tgl`).

## Coding (Ch 33): plural word *mga*

WALS Ch 33 codes Tagalog as "plural word." [schachter-otanes-1972]
§3.9 (p. 111) calls *mga* (phonemic /maŋah/, orthographic per
[himmelmann-2005-tagalog] p. 353) a **PROCLITIC** — not an article,
not a free word. It has two readings: plural ('the children') and
approximative with cardinals ('about ten'). [kroeger-1991-thesis]
treats it as enclitic on the preceding case marker (cf. p. 22 ex. 2:
*ang=mga=bata?* `NOM=PL=child`), without arguing the analysis.

Distribution restrictions ([schachter-otanes-1972] p. 112): *mga*
does NOT occur with cardinal numbers (*sampung anak* 'ten children', not
\\**sampung mga anak*; *mga sampu* yields the approximative reading
'about ten'); does NOT occur after the personal-noun markers *si/ni/kay*;
and is non-obligatory throughout — "the pluralization of a noun need not
— and, in some cases in fact, cannot — be formally signaled if the
context makes the plural meaning clear" (p. 111).

## Associative plural (Ch 36): *sina*

For the associative reading ('X and associates'), Tagalog uses *sina X*
(personal-name plural marker + name); the *mga X* construction with a
proper-name complement carries a different meaning ('two or more people
with the same name', e.g. *ang mga Santos* 'the Santoses'). The contrast
is drawn explicitly in [schachter-otanes-1972] p. 113: "*mga*
construction is used to designate two or more people with the same name,
while the plural-marker construction is used to designate the person
named plus other people. Thus *ang mga Santos* is 'the Santoses', while
*sina Santos* is 'Santos and others (who may or may not also be named
Santos)'."

The personal-name marker paradigm *si/ni/kay* (sg) ↔ *sina/nina/kina* (pl)
is given as a single table by [schachter-otanes-1972] §3.9 (p. 113);
S&O analyse the plurals as **derived by suffixation of *-na*** (with a
vowel change for *kay → kina*), not as a suppletive paradigm.
[kroeger-1991-thesis] (p. 14 ex. 12) and [himmelmann-2005-tagalog]
(Table 12.2, p. 358) tabulate only the singular set; the plural set
surfaces in Kroeger's glosses (e.g. p. 25 ex. 7 *sina=Ben* 'Ben and the
others'; p. 124 ex. 33) but is not analytically discussed.

## Pronoun plurality (Ch 35) and clusivity gap

The substrate's `.personNumberStem` value matches WALS Ch 35 but
underdetermines Tagalog's actual paradigm: *kata* (1+2 minimal-inclusive,
the "we two" form per S&O Chart 7 p. 88), *tayo* (1+2 augmented-inclusive
covering any 1+2+others grouping per S&O p. 89 — not specifically 1+2+3),
and *kami* (1+3 exclusive) instantiate Cysouw's *minimal-augmented* type
(see `Tagalog.clusivitySystem` in
`Fragments/Tagalog/Pronouns.lean`). The full Table 12.2 paradigm from
[himmelmann-2005-tagalog] is also documented there.
-/

set_option autoImplicit false

namespace Tagalog

-- ============================================================================
-- Tagalog-specific extensions
-- ============================================================================
--
-- Per-language structured data that the WALS-shaped `PluralityProfile`
-- cannot represent. These are Tagalog-internal records (no substrate impact,
-- no other Fragment forced to fill them); promote to substrate only when a
-- second language attests the same structural pattern.

/-- Distributional facts about the *mga* proclitic per
    [schachter-otanes-1972] §3.9 (pp. 111–112). -/
structure MgaDistribution where
  /-- *mga* may co-occur with cardinal numerals. False per S&O p. 112:
      *sampung anak* 'ten children', not \\**sampung mga anak*; with
      cardinals, *mga* yields the approximative reading instead (see
      `approximativeWithCardinals`). -/
  withCardinals : Bool
  /-- *mga* may follow the personal-noun markers *si/ni/kay*. False per
      S&O p. 112; the personal-name plural paradigm *sina/nina/kina*
      occupies that slot (see `personalNameMarkers`). -/
  withPersonalNameMarkers : Bool
  /-- *mga* with mass nouns is restricted: "mass nouns... normally do
      not occur freely with *mga*" ([schachter-otanes-1972] p. 112).
      The marker IS attested with mass nouns under two specific readings:
      "several masses" (*mga balita* 'news.PL') or with an implied
      deleted count noun (*mga tubig* = *mga baso ng tubig* 'glasses of
      water'). Encoded as `true` in the conditional sense; the
      defaults-are-blocked sense is documented in this comment. -/
  withMassNouns : Bool
  /-- *mga* applies in adjective phrases (S&O §4.11 pp. 229–230). True. -/
  withAdjectives : Bool
  /-- With cardinal numerals *mga* yields an approximative ('about N')
      reading rather than a plural one (S&O p. 111: *mga sampu* 'about
      ten', *mga ala una* 'about one o'clock'). True. -/
  approximativeWithCardinals : Bool
  /-- Plural marking is non-obligatory throughout: "the pluralization of
      a noun need not — and, in some cases in fact, cannot — be formally
      signaled if the context makes the plural meaning clear" (S&O p. 111). -/
  optional : Bool
  deriving Repr

/-- The Tagalog *mga* distribution per [schachter-otanes-1972] pp. 111–112. -/
def mgaDistribution : MgaDistribution :=
  { withCardinals := false
  , withPersonalNameMarkers := false
  , withMassNouns := true
  , withAdjectives := true
  , approximativeWithCardinals := true
  , optional := true }

/-- The Tagalog personal-name marker paradigm per [schachter-otanes-1972]
    §3.9 (pp. 93, 113). Three cases × two numbers; the plurals are
    derived by *-na* suffixation, with a vowel change for *kay → kina*. -/
structure PersonalNameMarkers where
  nomSg : String
  nomPl : String
  genSg : String
  genPl : String
  datSg : String
  datPl : String
  deriving Repr

/-- Tagalog personal-name markers per [schachter-otanes-1972] p. 113. -/
def personalNameMarkers : PersonalNameMarkers :=
  { nomSg := "si",  nomPl := "sina"
  , genSg := "ni",  genPl := "nina"
  , datSg := "kay", datPl := "kina" }

/-- The NOM and GEN plural personal-name markers are formed by suffixing
    *-na* to the singular, per [schachter-otanes-1972] p. 113. -/
theorem personalNameMarkers_na_suffixation_regular :
    personalNameMarkers.nomPl = personalNameMarkers.nomSg ++ "na" ∧
    personalNameMarkers.genPl = personalNameMarkers.genSg ++ "na" :=
  ⟨rfl, rfl⟩

/-- The DAT plural *kina* is NOT formed by simple *-na* suffixation:
    *kay + na ≠ kina*. S&O p. 113 describes a vowel change /ay/ → /i/
    accompanying the *-na* affix. The exceptional shape is what makes
    the paradigm worth tabulating; the regular cases follow
    `personalNameMarkers_na_suffixation_regular`. -/
theorem personalNameMarkers_dat_irregular :
    personalNameMarkers.datPl ≠ personalNameMarkers.datSg ++ "na" := by
  decide

end Tagalog
