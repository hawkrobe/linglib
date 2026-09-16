import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Kannada indefinite pronouns

Kannada builds its indefinite pronouns by suffixing a particle to an interrogative pronoun:
*yāru-oo* 'someone', on *yāru* 'who', for a referent the speaker presupposes but cannot
identify, and *yāru-aadaruu* 'anyone' for irrealis non-specific reference. Neither is used for a
referent the speaker has in mind.

## References

* [degano-aloni-2025]
* [haspelmath-1997]
-/

namespace Kannada.Indefinites

open Indefinite

/-- The *-oo* series, *yāru-oo* 'someone': on an interrogative base, for a referent the speaker
cannot identify. -/
def ooEntry : IndefinitePronoun where
  form := "yāru-oo"
  ontology := .person
  basis := .interrogative
  functions := {.specificUnknown}

/-- The *-aadaruu* series, *yāru-aadaruu* 'anyone': on an interrogative base, for irrealis
non-specific reference. -/
def aadaruuEntry : IndefinitePronoun where
  form := "yāru-aadaruu"
  ontology := .person
  basis := .interrogative
  functions := {.irrealis}

/-- The Kannada paradigm: no series for a referent the speaker has in mind. -/
def paradigm : IndefiniteParadigm := [ooEntry, aadaruuEntry]

end Kannada.Indefinites
