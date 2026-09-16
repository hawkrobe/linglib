import Linglib.Syntax.Clause.Relative

/-!
# Turkish relative clauses

Turkish relative clauses precede their head and their verb is a participle, *-(y)En* when the
head is the subject and *-DIK* otherwise, with the subject of the clause in the genitive. With
the relativized position left empty this relativizes subjects through obliques. Below that a
pronominal element is retained, a possessive suffix on the head noun for genitives and a
stressed pronoun for objects of comparison, the latter with reduced acceptability. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

namespace Turkish

open RelativeClause

/-- The prenominal participial clause leaves the relativized position empty and relativizes
subjects through obliques. -/
def relParticiple : Marker :=
  { form := "-(y)En/-DIK"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject, .directObject, .indirectObject, .oblique} }

/-- The prenominal participial clause with a retained pronominal element relativizes genitives
and, marginally, objects of comparison. -/
def relRetention : Marker :=
  { form := "-(y)En/-DIK + pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .preNominal
  , positions := {.genitive, .objComparison} }

/-- The Turkish relative-clause markers. -/
def relMarkers : List Marker := [relParticiple, relRetention]

end Turkish
