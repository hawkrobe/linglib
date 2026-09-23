import Linglib.Fragments.German.Pronouns

/-!
# German reciprocals

German marks reciprocity with the reciprocal pronoun *einander* and with *sich*, the form of the
third person reflexive. On [siloni-2012]'s analysis (footnotes 13 and 38), *einander* is a
reciprocal anaphor in an argument position, while the phonologically weak *sich* marks a
syntactically formed reciprocal verb, as Romance *se* does: embedded under *sagen* 'say', a
*sich* reciprocal lacks the "I" reading that *einander* allows. With one marker that is also
reflexive and one that is not, German is the example [maslova-nedjalkov-2013] give of the mixed
type, and WALS codes it so (`ofInventory_markers_eq_wals`).

## References

* [T. Siloni, *Reciprocal Verbs and Symmetry* (2012)][siloni-2012]
* [E. Maslova and V. P. Nedjalkov, *Reciprocal Constructions* (2013)][maslova-nedjalkov-2013]
-/

namespace German.Reciprocals

open Reciprocal

/-- The marker of the reciprocal pronoun *einander*. -/
def einander : Marker := Pronouns.einander.toMarker

/-- *sich* in its reciprocal use, the form of the reflexive pronoun. Its weak occurrence marks
the predicate rather than filling the object slot ([siloni-2012]). -/
def sich : Marker :=
  { form := Pronouns.sich.form, strategy := .recipClitic, readings := {.reciprocal, .reflexive} }

/-- The reciprocal marker inventory. -/
def markers : Finset Marker := {einander, sich}

/-- German has a reflexive and a non-reflexive reciprocal marker, the mixed type of
[maslova-nedjalkov-2013]. -/
theorem ofInventory_markers : ofInventory markers = .mixed := by decide

/-- The inventory computes the WALS value of German ([maslova-nedjalkov-2013]). -/
theorem ofInventory_markers_eq_wals :
    some (ofInventory markers) = (Data.WALS.F106A.lookupISO "deu").map (·.value) := by
  decide +kernel

end German.Reciprocals
