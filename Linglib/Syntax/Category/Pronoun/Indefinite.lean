module

public import Linglib.Semantics.Quantification.Indefinite
public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Indefinite pronouns

An indefinite pronoun is a pronoun with a place in an indefinite series: the ontological
category it belongs to and the morphological basis the series is built from. The functions a
series covers on [haspelmath-1997]'s implicational map are an analysis of its distribution and
not a lexical property, so they are paired with the entry in `Studies/Haspelmath1997.lean`,
which also states the adjacency requirement on them.

## Main declarations

* `IndefinitePronoun` — a pronoun with its ontological category and the morphological basis
  of its series
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

/-- An indefinite's token is of UD pronoun type `Ind`. -/
def IndefinitePronoun.toWord (p : IndefinitePronoun) : Morphology.Word :=
  p.toPronoun.toWord (some .Ind)
