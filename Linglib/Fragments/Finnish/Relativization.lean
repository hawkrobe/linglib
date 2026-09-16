import Linglib.Syntax.Clause.Relative

/-!
# Finnish relative clauses

Finnish has two relative-clause strategies. The relative pronoun *joka* declines for the case of
the relativized position and introduces a postnominal clause; it relativizes subjects through
genitives. A participial clause precedes its head with no relativizer and the relativized
position left empty, the participle differing according to whether the head is its subject or
its object, as in *pöydällä tanssinut poika* 'the boy who had danced on the table' and
*näkemäni poika* 'the boy that I saw'; it relativizes subjects and direct objects only. Finnish
is the paper's example of a language whose broader, primary strategy is the case-coding one.
The data are [keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

namespace Finnish

open RelativeClause

/-- The relative pronoun *joka* declines for the case of the relativized position and relativizes
subjects through genitives. -/
def relJoka : Marker :=
  { form := "joka"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , placement := .postNominal
  , positions := {.subject, .directObject, .indirectObject, .oblique, .genitive} }

/-- The prenominal participial clause leaves the relativized position empty and relativizes
subjects and direct objects only. -/
def relParticipial : Marker :=
  { form := "participle"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject, .directObject} }

/-- The Finnish relative-clause markers. -/
def relMarkers : List Marker := [relJoka, relParticipial]

end Finnish
