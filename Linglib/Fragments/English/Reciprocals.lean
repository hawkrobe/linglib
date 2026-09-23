import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Verbs
import Linglib.Syntax.Reciprocal

/-!
# English reciprocals

English marks reciprocity with the two-part noun phrases *each other* and *one another*, which
fill an argument slot of a bivalent clause and are distinct from the reflexive *themselves*. A
closed class of predicates such as *meet*, *quarrel* and *kiss* is reciprocal without any marker.
The markers are those of the pronoun entries in `Fragments/English/Pronouns.lean`. The lexical
strategy has no exponent, so the verb entries carry it and it does not feed
`Reciprocal.ofInventory`, which classifies constructions.

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [T. Siloni, *Reciprocal Verbs and Symmetry* (2012)][siloni-2012]
* [E. Maslova and V. P. Nedjalkov, *Reciprocal Constructions* (2013)][maslova-nedjalkov-2013]
-/

namespace English.Reciprocals

open Reciprocal

/-- The marker of *each other*, from its pronoun entry. -/
def eachOther : Marker := Pronouns.eachOther.toMarker

/-- The marker of *one another*, from its pronoun entry. -/
def oneAnother : Marker := Pronouns.oneAnother.toMarker

/-- The inherently reciprocal predicates, as verb entries: the lexical strategy marks
predicates, not forms ([nordlinger-2023], [siloni-2012]). -/
def lexicalReciprocals : List English.Verb :=
  [English.meet]

/-- The reciprocal marker inventory. -/
def markers : Finset Marker := {eachOther, oneAnother}

/-- The inventory computes the WALS value of English ([maslova-nedjalkov-2013]). -/
theorem ofInventory_markers_eq_wals :
    some (ofInventory markers) = (Data.WALS.F106A.lookupISO "eng").map (·.value) := by
  decide +kernel

end English.Reciprocals
