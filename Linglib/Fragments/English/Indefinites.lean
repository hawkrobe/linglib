module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# English indefinite pronouns

English builds its indefinite pronouns on generic nouns: *some-*, *any-* and *no-* prefixed to
*-one*, *-body*, *-thing* and *-where*. The *some-* series is used for a referent the speaker
has in mind, for one the speaker presupposes but cannot identify and for irrealis non-specific
reference, and reaches into questions and conditionals; the *any-* series takes over from
questions and conditionals through both negations and the comparative to free choice; the *no-*
series is confined to direct negation. The two longer series overlap in questions and
conditionals (*Did you see someone?*, *Did you see anyone?*).

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace English.Indefinites

/-- The *some-* series, *someone*, *somebody*, *something*: the three specific functions,
questions and conditionals. -/
def someEntry : IndefinitePronoun where
  form := "someone"
  ontology := .person
  basis := .genericNoun

/-- The *any-* series, *anyone*, *anybody*, *anything*: from questions and conditionals through
both negations and the comparative to free choice. -/
def anyEntry : IndefinitePronoun where
  form := "anyone"
  ontology := .person
  basis := .genericNoun

/-- The *no-* series, *no one*, *nobody*, *nothing*: direct negation. -/
def noEntry : IndefinitePronoun where
  form := "no one"
  ontology := .person
  basis := .genericNoun

/-- The English paradigm: the *some-*, *any-* and *no-* series. -/
def paradigm : List IndefinitePronoun := [someEntry, anyEntry, noEntry]

end English.Indefinites
