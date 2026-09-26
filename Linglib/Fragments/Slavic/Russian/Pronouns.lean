module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Russian interrogative pronouns

This file defines the Russian interrogative pronouns *kto* 'who' and *čto* 'what' ([wade-2020]
§121), each with the ontological category it asks about. *Kto* is used for people, *čto* for
things. They are the bases of the indefinite series of `Russian.Indefinites`.

## References

* [wade-2020]
-/

@[expose] public section

namespace Russian.Pronouns

/-- *kto* (кто) 'who' asks about a person. -/
def kto : InterrogativePronoun := { form := "kto", ontology := .person }

/-- *čto* (что) 'what' asks about a thing. -/
def čto : InterrogativePronoun := { form := "čto", ontology := .thing }

end Russian.Pronouns
