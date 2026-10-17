module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Kannada indefinite pronouns

Kannada builds its indefinite pronouns by suffixing a particle to an interrogative pronoun,
three series on *yaaru* 'who': *yaar-oo* 'someone', with *-oo* 'or', for a referent the speaker
presupposes but cannot identify; *yaar-aadaruu* 'anyone', with *-aadaruu* 'even if it be', for
irrealis non-specific reference and in questions and conditionals; and *yaar-uu*, with *-uu*
'also, even', under negation, in comparatives and for free choice. No series is used for a
referent the speaker has in mind. Each series is entered with its person member.

## References

* [degano-aloni-2025]
* [haspelmath-1997]
-/

@[expose] public section

namespace Kannada.Indefinites

/-- *yaar-oo* 'someone'. -/
def yaarOo : IndefinitePronoun where
  form := "yaar-oo"
  ontology := .person
  basis := .interrogative

/-- *yaar-aadaruu* 'anyone'. -/
def yaarAadaruu : IndefinitePronoun where
  form := "yaar-aadaruu"
  ontology := .person
  basis := .interrogative

/-- *yaar-uu* 'anyone, no one'. -/
def yaarUu : IndefinitePronoun where
  form := "yaar-uu"
  ontology := .person
  basis := .interrogative

/-! ### The series -/

/-- The *-oo* series. -/
def ooSeries : IndefinitePronoun.Series := ⟨"-oo", [yaarOo]⟩

/-- The *-aadaruu* series. -/
def aadaruuSeries : IndefinitePronoun.Series := ⟨"-aadaruu", [yaarAadaruu]⟩

/-- The *-uu* series. -/
def uuSeries : IndefinitePronoun.Series := ⟨"-uu", [yaarUu]⟩

end Kannada.Indefinites
