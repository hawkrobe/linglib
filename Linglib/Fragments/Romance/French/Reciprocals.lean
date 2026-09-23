import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Reciprocal

/-!
# French reciprocals

French marks reciprocity with the clitic *se*, shared with the reflexive, and with the bipartite
*l'un l'autre* 'the one the other', which fills an argument position, keeps the clause bivalent and
often accompanies *se* to disambiguate it. Reciprocal verbs with *se* are formed in the syntax
([siloni-2008]), so they have no discontinuous counterpart with *avec* 'with' ([nordlinger-2023] ex.
39).

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [T. Siloni, *The Syntax of Reciprocal Verbs: An Overview* (2008)][siloni-2008]
-/

namespace French.Reciprocals

open Reciprocal

/-- se — reflexive/reciprocal clitic ([nordlinger-2023] ex. 28, 47). -/
def se : Marker :=
  { form := "se", strategy := .recipClitic
  , readings := {.reciprocal, .reflexive} }

/-- l'un l'autre — bipartite reciprocal NP. -/
def lunLautre : Marker :=
  { form := "l'un l'autre", strategy := .bipartiteNP }

/-- Marker inventory. -/
def markers : Finset Marker := {se, lunLautre}

end French.Reciprocals
