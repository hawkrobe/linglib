import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Yakut (Sakha) indefinite pronouns

Yakut builds its indefinite pronouns from an interrogative pronoun and an enclitic particle,
four series on *kim* 'who': *kim ere* 'somebody' for a referent the speaker has in mind or
presupposes; *kim eme* 'somebody, anybody' for irrealis non-specific reference and in questions
and conditionals; *kim da* 'anybody', with the variant *kim dayanï*, in affirmative and negative
sentences alike, under negation, in comparatives and for free choice; and the generalising
*kim bayarar* 'whoever', on *bayar* 'want', for free choice.

## References

* [haspelmath-1997]
* [stachowski-menz-1998]
-/

namespace Yakut.Indefinites

/-- *Kim ere* 'somebody': for a referent the speaker has in mind or presupposes. -/
def ereEntry : IndefinitePronoun where
  form := "kim ere"
  ontology := .person
  basis := .interrogative

/-- *Kim eme* 'somebody, anybody': for irrealis non-specific reference and in questions and
conditionals. -/
def emeEntry : IndefinitePronoun where
  form := "kim eme"
  ontology := .person
  basis := .interrogative

/-- *Kim da* 'anybody', with the variant *kim dayanï*: under both negations, in comparatives
and for free choice. -/
def daEntry : IndefinitePronoun where
  form := "kim da"
  ontology := .person
  basis := .interrogative

/-- *Kim bayarar* 'whoever': for free choice. -/
def bayararEntry : IndefinitePronoun where
  form := "kim bayarar"
  ontology := .person
  basis := .interrogative

/-- The Yakut paradigm: four series on *kim*. -/
def paradigm : List IndefinitePronoun := [ereEntry, emeEntry, daEntry, bayararEntry]

end Yakut.Indefinites
