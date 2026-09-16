import Linglib.Syntax.Clause.Relative

/-!
# Basque relative clauses

Basque has one relative-clause strategy. The clause precedes its head, the relativized position
is left empty, and the juncture is marked by the invariable suffix *-n*, as in *emakumeari
liburua eman dion gizona* 'the man who has given the book to the woman'. It relativizes
subjects, direct objects and indirect objects, the three positions cross-referenced on the
verb; the paper offers Basque as the language whose cut-off falls exactly at the indirect
object, and records no data for the lower positions. The data are [keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

namespace Basque

open RelativeClause

/-- The prenominal clause closed by the suffix *-n* leaves the relativized position empty and
relativizes subjects, direct objects and indirect objects. -/
def relN : Marker :=
  { form := "-n"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject, .directObject, .indirectObject} }

/-- The Basque relative-clause markers. -/
def relMarkers : List Marker := [relN]

end Basque
