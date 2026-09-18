import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Yakut (Sakha) indefinite pronouns

Yakut builds its indefinite pronouns from an interrogative pronoun and an enclitic particle, four
series on *kim* 'who' as Stachowski and Menz describe them: *kim ere* 'somebody' for a referent
the speaker has in mind or presupposes, *kim eme* 'somebody, anybody' for irrealis non-specific
reference, *kim bayarar* 'whoever' for free choice and in conditionals, and *kim da* 'anybody',
with the variant *kim dayanï*, in questions, conditionals and comparatives and under direct and
indirect negation.

## References

* [haspelmath-1997]
* [stachowski-menz-1998]
-/

namespace Yakut.Indefinites

open Indefinite

/-- *Kim ere* 'somebody': for a referent the speaker has in mind or presupposes. -/
def ereEntry : IndefinitePronoun where
  form := "kim ere"
  ontology := .person
  basis := .interrogative
  functions := {.specificKnown, .specificUnknown}

/-- *Kim eme* 'somebody, anybody': for irrealis non-specific reference. -/
def emeEntry : IndefinitePronoun where
  form := "kim eme"
  ontology := .person
  basis := .interrogative
  functions := {.irrealis}

/-- *Kim bayarar* 'whoever': for free choice and in conditionals. -/
def bayararEntry : IndefinitePronoun where
  form := "kim bayarar"
  ontology := .person
  basis := .interrogative
  functions := {.freeChoice, .conditional}

/-- *Kim da* 'anybody', with the variant *kim dayanï*: in questions, conditionals and
comparatives and under both negations. -/
def daEntry : IndefinitePronoun where
  form := "kim da"
  ontology := .person
  basis := .interrogative
  functions := {.question, .conditional, .comparative, .indirectNeg, .directNeg}

/-- The Yakut paradigm: four series on *kim*. -/
def paradigm : List IndefinitePronoun := [ereEntry, emeEntry, bayararEntry, daEntry]

end Yakut.Indefinites
