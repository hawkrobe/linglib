import Linglib.Syntax.Reciprocal

/-!
# Modern Greek reciprocals

Modern Greek marks reciprocity with nonactive verbal morphology, which also expresses
reflexives, passives and middles, and with the periphrastic *o enas ton allon* 'the one the
other'. Nonactive reciprocal verbs form discontinuous reciprocals with *me* 'with' (*O Giannis
filithike me ti Maria* 'John and Maria kissed each other', [nordlinger-2023] exx. 27b, 36, from
[dimitriadis-2008]), which on [siloni-2008]'s analysis marks lexical formation. With a
reflexive and a non-reflexive marker, Greek is the mixed type of [maslova-nedjalkov-2013].

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [T. Siloni, *The Syntax of Reciprocal Verbs: An Overview* (2008)][siloni-2008]
* [A. Dimitriadis, *Irreducible Symmetry in Reciprocal Constructions* (2008)][dimitriadis-2008]
* [E. Maslova and V. P. Nedjalkov, *Reciprocal Constructions* (2013)][maslova-nedjalkov-2013]
-/

namespace Greek.StandardModern.Reciprocals

open Reciprocal

def nonactive : Marker :=
  { form := "-ome", strategy := .verbalAffix
  , readings := {.reciprocal, .reflexive} }

/-- o enas ton allon — distinct periphrastic reciprocal, whose existence
    underlies the WALS "mixed" classification ([maslova-nedjalkov-2013]). -/
def oEnasTonAllon : Marker :=
  { form := "o enas ton allon", strategy := .bipartiteNP }

/-- Marker inventory. -/
def markers : Finset Marker := {nonactive, oEnasTonAllon}

/-- The inventory computes the WALS value of Greek ([maslova-nedjalkov-2013]). -/
theorem ofInventory_markers_eq_wals :
    some (ofInventory markers) = (Data.WALS.F106A.lookupISO "ell").map (·.value) := by
  decide +kernel

end Greek.StandardModern.Reciprocals
