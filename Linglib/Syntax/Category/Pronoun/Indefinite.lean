module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Indefinite pronouns

An indefinite pronoun is a pronoun with a place in an indefinite series: the ontological
category it belongs to and the morphological basis the series is built from. The functions a
series covers on [haspelmath-1997]'s implicational map are an analysis of its distribution and
not a lexical property, so they are paired with the entry in `Studies/Haspelmath1997.lean`,
which also states the adjacency requirement on them. A series built on the interrogatives marks
each interrogative with the same affix or particle, and `IndefinitePronoun.ofInterrogative`
builds its members so.

## Main declarations

* `IndefinitePronoun` — a pronoun with its ontological category and the morphological basis
  of its series
* `IndefinitePronoun.ofInterrogative` — the indefinite a marker builds on an interrogative
* `IndefinitePronoun.toWord` — its token, of UD pronoun type `Ind`

## References

* [M. Haspelmath, *Indefinite Pronouns* (1997)][haspelmath-1997]
-/

@[expose] public section

/-- An indefinite pronoun: its surface form and φ-features as a `Pronoun`, with its ontological
category and the morphological basis of its series. -/
structure IndefinitePronoun extends Pronoun where
  /-- The ontological category of the pronoun within its series. -/
  ontology : Indefinite.OntologicalCategory
  /-- The morphological basis the series is built from. -/
  basis : Indefinite.MorphologicalBasis
  deriving DecidableEq

instance : HasPhi IndefinitePronoun := ⟨fun e ↦ e.toPronoun.phi⟩

/-- The indefinite a series marker builds on an interrogative pronoun, as Russian *-nibud'* builds
*kto-nibud'* on *kto*: the interrogative's features and category, with the marked form, in a
series of interrogative basis. -/
@[simps ontology basis]
def IndefinitePronoun.ofInterrogative (mark : String → String) (q : InterrogativePronoun) :
    IndefinitePronoun :=
  { q.toPronoun with form := mark q.form, ontology := q.ontology, basis := .interrogative }

/-- An indefinite's token is of UD pronoun type `Ind`. -/
def IndefinitePronoun.toWord (p : IndefinitePronoun) : Morphology.Word :=
  p.toPronoun.toWord (some .Ind)
