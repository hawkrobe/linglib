module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# English indefinite pronouns

English prefixes *some-*, *any-* and *no-* to the generic nouns *one*, *body* and *thing* and to the
interrogative *where*, so that its series mix bases. The *some-* series is used for a referent the
speaker has in mind, for one the speaker presupposes but cannot identify and for irrealis
non-specific reference, and reaches into questions and conditionals; the *any-* series takes over
from questions and conditionals through both negations and the comparative to free choice; the *no-*
series is confined to direct negation. The two longer series overlap in questions and conditionals
(*Did you see someone?*, *Did you see anyone?*). Each series is entered with its person member.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace English.Indefinites

/-- *someone*, the person member of the *some-* series. -/
def someone : IndefinitePronoun where
  form := "someone"
  ontology := .person
  basis := .genericNoun

/-- *anyone*, the person member of the *any-* series. -/
def anyone : IndefinitePronoun where
  form := "anyone"
  ontology := .person
  basis := .genericNoun

/-- *no one*, the person member of the *no-* series. -/
def noOne : IndefinitePronoun where
  form := "no one"
  ontology := .person
  basis := .genericNoun

/-! ### The series -/

/-- The *some-* series. -/
def someSeries : IndefinitePronoun.Series := ⟨"some-", [someone]⟩

/-- The *any-* series. -/
def anySeries : IndefinitePronoun.Series := ⟨"any-", [anyone]⟩

/-- The *no-* series. -/
def noSeries : IndefinitePronoun.Series := ⟨"no-", [noOne]⟩

end English.Indefinites
