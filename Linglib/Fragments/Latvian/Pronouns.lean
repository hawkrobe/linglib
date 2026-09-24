module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Latvian pronouns

The interrogative pronouns of Latvian, by the ontological category they ask about: *kas* asks
about persons and things alike, *kur* about places, *kad* about times and *kā* about manners,
and *kāds* 'which, what kind of' and *kurš* 'which' are determiners. They are the bases of the
indefinite series of `Latvian.Indefinites`.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Latvian.Pronouns

/-- *kas* 'who', asking about a person. -/
def kasPerson : InterrogativePronoun := { form := "kas", ontology := .person }

/-- *kas* 'what', the same form asking about a thing. -/
def kasThing : InterrogativePronoun := { form := "kas", ontology := .thing }

/-- *kur* 'where'. -/
def kur : InterrogativePronoun := { form := "kur", ontology := .place }

/-- *kad* 'when'. -/
def kad : InterrogativePronoun := { form := "kad", ontology := .time }

/-- *kā* 'how'. -/
def kā : InterrogativePronoun := { form := "kā", ontology := .manner }

/-- *kāds* 'which, what kind of', a determiner. -/
def kāds : InterrogativePronoun := { form := "kāds", ontology := .determiner }

/-- *kurš* 'which', a determiner. -/
def kurš : InterrogativePronoun := { form := "kurš", ontology := .determiner }

end Latvian.Pronouns
