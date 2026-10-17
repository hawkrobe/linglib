module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Yakut (Sakha) indefinite pronouns

Yakut builds its indefinite pronouns from an interrogative pronoun and an enclitic particle,
four series on *kim* 'who': *kim ere* 'somebody' for a referent the speaker has in mind or
presupposes; *kim eme* 'somebody, anybody' for irrealis non-specific reference and in questions
and conditionals; *kim da* 'anybody', with the variant *kim dayanï*, in affirmative and negative
sentences alike, under negation, in comparatives and for free choice; and the generalising
*kim bayarar* 'whoever', on *bayar* 'want', for free choice. Each series is entered with its
person member.

## References

* [haspelmath-1997]
* [stachowski-menz-1998]
-/

@[expose] public section

namespace Yakut.Indefinites

/-- *kim ere* 'somebody'. -/
def kimEre : IndefinitePronoun where
  form := "kim ere"
  ontology := .person
  basis := .interrogative

/-- *kim eme* 'somebody, anybody'. -/
def kimEme : IndefinitePronoun where
  form := "kim eme"
  ontology := .person
  basis := .interrogative

/-- *kim da* 'anybody', with the variant *kim dayanï*. -/
def kimDa : IndefinitePronoun where
  form := "kim da"
  ontology := .person
  basis := .interrogative

/-- *kim bayarar* 'whoever'. -/
def kimBayarar : IndefinitePronoun where
  form := "kim bayarar"
  ontology := .person
  basis := .interrogative

/-! ### The series -/

/-- The *ere* series. -/
def ereSeries : IndefinitePronoun.Series := ⟨"ere", [kimEre]⟩

/-- The *eme* series. -/
def emeSeries : IndefinitePronoun.Series := ⟨"eme", [kimEme]⟩

/-- The *da* series. -/
def daSeries : IndefinitePronoun.Series := ⟨"da", [kimDa]⟩

/-- The *bayarar* series. -/
def bayararSeries : IndefinitePronoun.Series := ⟨"bayarar", [kimBayarar]⟩

end Yakut.Indefinites
