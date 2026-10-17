module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Russian interrogative pronouns

The Russian interrogative pronouns, each with the ontological category it asks about: *kto*
'who' for people and *čto* 'what' for things, as Wade describes them, and *gde* 'where', *kogda*
'when', *kak* 'how', *skol'ko* 'how much' and the determiner *kakoj*, which Haspelmath tabulates
with them. They are the bases of the indefinite series of `Russian.Indefinites`.

## References

* [haspelmath-1997]
* [wade-2020]
-/

@[expose] public section

namespace Russian.Pronouns

/-- *kto* (кто) 'who' asks about a person ([wade-2020] §121). -/
def kto : InterrogativePronoun := { form := "kto", ontology := .person }

/-- *čto* (что) 'what' asks about a thing ([wade-2020] §121). -/
def čto : InterrogativePronoun := { form := "čto", ontology := .thing }

/-- *gde* 'where' asks about a place. -/
def gde : InterrogativePronoun := { form := "gde", ontology := .place }

/-- *kogda* 'when' asks about a time. -/
def kogda : InterrogativePronoun := { form := "kogda", ontology := .time }

/-- *kak* 'how' asks about a manner. -/
def kak : InterrogativePronoun := { form := "kak", ontology := .manner }

/-- *skol'ko* 'how much' asks about an amount. -/
def skol'ko : InterrogativePronoun := { form := "skol'ko", ontology := .amount }

/-- *kakoj* 'which' is the interrogative determiner. -/
def kakoj : InterrogativePronoun := { form := "kakoj", ontology := .determiner }

/-- The interrogatives on which the indefinite series are built. -/
def interrogatives : Finset InterrogativePronoun := {kto, čto, gde, kogda, kak, skol'ko, kakoj}

end Russian.Pronouns
