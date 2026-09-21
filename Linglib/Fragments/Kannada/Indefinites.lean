import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Kannada indefinite pronouns

Kannada builds its indefinite pronouns by suffixing a particle to an interrogative pronoun,
three series on *yaaru* 'who': *yaar-oo* 'someone', with *-oo* 'or', for a referent the speaker
presupposes but cannot identify; *yaar-aadaruu* 'anyone', with *-aadaruu* 'even if it be', for
irrealis non-specific reference and in questions and conditionals; and *yaar-uu*, with *-uu*
'also, even', under negation, in comparatives and for free choice. No series is used for a
referent the speaker has in mind.

## References

* [degano-aloni-2025]
* [haspelmath-1997]
-/

namespace Kannada.Indefinites

/-- The *-oo* series, *yaar-oo* 'someone': for a referent the speaker cannot identify. -/
def ooEntry : IndefinitePronoun where
  form := "yaar-oo"
  ontology := .person
  basis := .interrogative

/-- The *-aadaruu* series, *yaar-aadaruu* 'anyone': for irrealis non-specific reference and in
questions and conditionals. -/
def aadaruuEntry : IndefinitePronoun where
  form := "yaar-aadaruu"
  ontology := .person
  basis := .interrogative

/-- The *-uu* series, *yaar-uu* 'anyone, no one': under both negations, in comparatives and
for free choice. -/
def uuEntry : IndefinitePronoun where
  form := "yaar-uu"
  ontology := .person
  basis := .interrogative

/-- The Kannada paradigm: no series for a referent the speaker has in mind. -/
def paradigm : List IndefinitePronoun := [ooEntry, aadaruuEntry, uuEntry]

end Kannada.Indefinites
