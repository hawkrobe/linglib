module

public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Number.Basic

/-!
# Tagalog case markers

Tagalog marks the case of a noun phrase with a proclitic marker rather than on the noun: *ang*
for the subject, *ng* for possessors and for non-subject agents and objects, and *sa* for
obliques, the series Himmelmann labels specifier, possessive and locative and Kroeger
nominative, genitive and dative. Personal names take *si*, *ni* and *kay* instead, with the
plurals *sina*, *nina* and *kina*, which Schachter and Otanes analyse as the singular markers
with the suffix *-na*, *kay* changing its vowel. *Sina Santos* denotes Santos with associates,
where the common plural *ang mga Santos* denotes several people named Santos. Common nouns
pluralize with the proclitic *mga* after the case marker, which Schachter and Otanes describe as
optional where the context makes the plural clear, as absent with cardinal numerals, with which
it gives an approximative reading instead, and as restricted with mass nouns.

## Main definitions

* `Tagalog.marker` — the common-noun case markers
* `Tagalog.personalMarker` — the personal-name case markers by number
* `Tagalog.plural` — the plural proclitic *mga* of common nouns

## References

* [himmelmann-2005-tagalog]
* [kroeger-1991-thesis]
* [schachter-otanes-1972]
-/

@[expose] public section

namespace Tagalog

/-- The common-noun case markers *ang*, *ng* and *sa*. -/
def marker : Case → Option String
  | .nom => some "ang"
  | .gen => some "ng"
  | .dat => some "sa"
  | _ => none

/-- The personal-name case markers, singular *si*, *ni*, *kay* and plural *sina*, *nina*,
*kina*. -/
def personalMarker : Case → Number → Option String
  | .nom, .singular => some "si"
  | .gen, .singular => some "ni"
  | .dat, .singular => some "kay"
  | .nom, .plural => some "sina"
  | .gen, .plural => some "nina"
  | .dat, .plural => some "kina"
  | _, _ => none

/-- The plural proclitic *mga* of common nouns. -/
def plural : String := "mga"

end Tagalog
