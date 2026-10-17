module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Indefinite pronouns

An indefinite pronoun is a pronoun with the ontological category it stands for and the basis it
is built on. Indefinite pronouns come in series whose members are formed alike across the
categories, as the English *some*-series *somebody*, *something*, *somewhere*. The basis belongs
to the member, since a series may mix bases: *somebody* is built on a generic noun and
*somewhere* on an interrogative. The functions a series covers on Haspelmath's implicational map
are an analysis of its distribution, which studies pair with the series.

## Main definitions

* `IndefinitePronoun.Basis`: the four ways an indefinite is built.
* `IndefinitePronoun`: a pronoun with its ontological category and basis.
* `IndefinitePronoun.ofInterrogative`: the indefinite a marker builds on an interrogative.
* `IndefinitePronoun.toWord`: its token, of UD pronoun type `Ind`.
* `IndefinitePronoun.Series`: the members of a series, with the name it is cited by.

## References

* [haspelmath-1997]
* [wals-2013]
-/

@[expose] public section

/-- An indefinite is built on an interrogative pronoun (Russian *kto-nibud'*), on a generic noun
(English *somebody*), with a dedicated indefinite marker (German *irgend-*), or as an existential
construction. These are the four single-basis cells of chapter 46 of [wals-2013]; its fifth cell,
mixed, describes a paradigm using several bases. -/
inductive IndefinitePronoun.Basis where
  /-- The indefinite is built on an interrogative pronoun. -/
  | interrogative
  /-- The indefinite is built on a generic noun for person, thing or place. -/
  | genericNoun
  /-- The indefinite is built with a dedicated indefinite marker. -/
  | special
  /-- The indefinite is an existential construction. -/
  | existentialConstruction
  deriving DecidableEq, Repr

/-- An indefinite pronoun is a `Pronoun` with its ontological category and the basis it is
built on. -/
structure IndefinitePronoun extends Pronoun where
  /-- The ontological category the pronoun stands for. -/
  ontology : Pronoun.OntologicalCategory
  /-- The basis the pronoun is built on. -/
  basis : IndefinitePronoun.Basis
  deriving DecidableEq

namespace IndefinitePronoun

/-- The indefinite a series marker builds on an interrogative pronoun, as Russian *-nibud'* builds
*kto-nibud'* on *kto*. It has the interrogative's features and category and the marked form, and
is built on the interrogative. The marker acts on the romanized form, so the native script of the
marked form is left unrecorded. -/
@[simps ontology basis]
def ofInterrogative (mark : String → String) (q : InterrogativePronoun) : IndefinitePronoun :=
  { q.toPronoun with
    form := mark q.form, script := none, ontology := q.ontology, basis := .interrogative }

/-- An indefinite's token is of UD pronoun type `Ind`, with the word class its category
fixes. -/
def toWord (p : IndefinitePronoun) : Morphology.Word :=
  { p.toPronoun.toWord (some .Ind) with cat := p.ontology.upos }

/-- An indefinite series is the indefinite pronouns formed alike across the ontological
categories, as the English *some*-series *somebody*, *something*, *somewhere*. -/
structure Series where
  /-- The name the series is cited by, its marker where it has one, as *some-*, *-nibud'* or
  *ugodno*. -/
  name : String
  /-- The members, each with its ontological category. -/
  members : List IndefinitePronoun
  deriving DecidableEq

end IndefinitePronoun
