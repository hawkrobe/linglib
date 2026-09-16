import Linglib.Semantics.Quantification.Indefinite
import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Indefinite pronouns

An indefinite pronoun is a pronoun with a place in an indefinite series: the region of
[haspelmath-1997]'s implicational map its series covers, the ontological category it belongs to
and the morphological basis it is built from. A language's paradigm is the list of its series;
the adjacency requirement on each series and the syncretism of a paradigm across the specific
functions are the matter of `Studies/Haspelmath1997.lean` and `Studies/Dekier2021.lean`.

## Main declarations

* `Indefinite.IndefinitePronoun`: a pronoun with its series data, `extends Pronoun`.
* `Indefinite.IndefiniteParadigm`: a language's indefinite series.

## References

* [haspelmath-1997]
-/

namespace Indefinite

/-- An indefinite pronoun: its surface form and φ-features as a `Pronoun`, with the ontological
category and morphological basis of its series and the functions of the map the series covers.
The functions are the series' attested distribution, which a paradigm mate may narrow. -/
structure IndefinitePronoun extends Pronoun where
  /-- The ontological category of the series. -/
  ontology : OntologicalCategory
  /-- The morphological basis the series is built from. -/
  basis : MorphologicalBasis
  /-- The functions of the map the series covers. -/
  functions : Finset HaspelmathFunction
  deriving DecidableEq

instance : HasPhi IndefinitePronoun := ⟨fun e ↦ e.toPronoun.phi⟩

/-- A language's indefinite paradigm: its series. -/
abbrev IndefiniteParadigm := List IndefinitePronoun

end Indefinite
