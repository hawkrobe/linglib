import Linglib.Syntax.Clause.Relative

/-!
# Malagasy relative clauses

Malagasy relativizes subjects only. The head noun is followed, optionally, by the invariable
relativizer *izay* and then by the clause with the relativized position left empty, as in *ny
mpianatra izay nahita ny vehivavy* 'the student that saw the woman'. Any other noun phrase must
first be promoted to subject by the voice system and then relativized as a subject. The data
are [keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

namespace Malagasy

open RelativeClause

/-- The postnominal clause, optionally introduced by *izay*, leaves the relativized position
empty and relativizes subjects only. -/
def relGap : Marker :=
  { form := "izay/∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .postNominal
  , positions := {.subject} }

/-- The Malagasy relative-clause markers. -/
def relMarkers : List Marker := [relGap]

end Malagasy
