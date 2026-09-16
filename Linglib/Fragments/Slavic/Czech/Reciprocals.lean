import Linglib.Syntax.Reciprocal

/-!
# Czech reciprocals

Czech marks reciprocity with the reflexive clitic *se*, which also carries the reflexive
reading and yields a monovalent predicate, and with the bipartite periphrasis
*jeden druhého* 'one the-other' ([nordlinger-2023], [siloni-2012]). A reciprocal marker
shared with the reflexive beside a dedicated one is the mixed configuration of
[maslova-nedjalkov-2013] (`ofInventory_markers`).

## References

* [nordlinger-2023]
* [siloni-2012]
* [maslova-nedjalkov-2013]
-/

namespace Czech.Reciprocals

open Reciprocal

/-- *se*, the reflexive clitic in its reciprocal use. -/
def se : Marker :=
  { form := "se", strategy := .recipClitic, readings := {.reciprocal, .reflexive} }

/-- *jeden druhého* 'one the-other', the bipartite periphrastic reciprocal. -/
def jedenDruheho : Marker := { form := "jeden druhého", strategy := .bipartiteNP }

/-- The reciprocal markers, primary strategy first. -/
def markers : List Marker := [se, jedenDruheho]

/-- Czech is the mixed type of [maslova-nedjalkov-2013]: one reciprocal marker is also
reflexive, the other is not. -/
theorem ofInventory_markers : ofInventory markers = .mixed := by decide

end Czech.Reciprocals
