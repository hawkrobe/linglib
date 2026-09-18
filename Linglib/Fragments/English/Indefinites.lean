import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# English indefinite pronouns

English builds its indefinite pronouns on generic nouns: *some-* prefixed to *-one*, *-body*,
*-thing* and *-where* gives *someone*, *somebody*, *something* and *somewhere*, with parallel
*any-*, *no-* and *every-* series. The *some-* series is used alike for a referent the speaker
has in mind, for one the speaker presupposes but cannot identify, and for irrealis non-specific
reference.

## References

* [haspelmath-1997]
-/

namespace English.Indefinites

open Indefinite

/-- The *some-* series, *someone*, *somebody*, *something*: built on generic nouns and used in
all three specific functions. -/
def someEntry : IndefinitePronoun where
  form := "someone/-body/-thing"
  ontology := .person
  basis := .genericNoun
  functions := {.specificKnown, .specificUnknown, .irrealis}

/-- The English paradigm, its *some-* series; *any-* and *no-* are not entered. -/
def paradigm : List IndefinitePronoun := [someEntry]

end English.Indefinites
