import Linglib.Syntax.Clause.Relative

/-!
# Korean relative-clause markers

The Korean relativization strategies as [keenan-comrie-1977] records them. A prenominal clause
whose verb carries the adnominal suffix, with the relativized position deleted, relativizes
subjects through obliques; genitives require the same clause with the possessive pronoun
retained, as in the paper's *chaki-ij lä-ka chongmyəngha-n kɨ salam* 'the man whose dog is
smart'. Korean has no relative pronoun or complementizer.

## References

* [keenan-comrie-1977]
-/

namespace Korean

open RelativeClause

/-- The adnominal verb suffix (*-(n)ɨn* present, *-n* past, *-l* prospective) forms a prenominal
clause whose relativized position and its case marker are deleted; it relativizes subjects
through obliques. -/
def relAdnominal : Marker :=
  { form := "-(n)ɨn, -n, -l"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject, .directObject, .indirectObject, .oblique} }

/-- The adnominal clause with the possessive pronoun retained at the relativized position, the
only strategy for genitives. -/
def relGenitive : Marker :=
  { form := "-(ɨ)n + retained pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .preNominal
  , positions := {.genitive} }

/-- The Korean relative-clause markers. -/
def relMarkers : List Marker := [relAdnominal, relGenitive]

end Korean
