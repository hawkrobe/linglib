import Linglib.Syntax.Clause.Relative

/-!
# Korean relative clauses

Korean has no relative pronoun and no complementizer. A relative clause precedes its head noun
and its verb carries an adnominal suffix, *-(n)ɨn* in the present, *-n* in the past and *-l* in
the prospective; the relativized position is dropped together with its case marker, and this
strategy relativizes subjects, direct objects, indirect objects and obliques. A genitive cannot
be dropped: the possessive pronoun is retained, as in *chaki-ij lä-ka chongmyəngha-n kɨ salam*
'the man whose dog is smart', literally 'his dog is smart, the man'. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

namespace Korean

open RelativeClause

/-- The adnominal clause with the relativized position dropped relativizes subjects, direct
objects, indirect objects and obliques. -/
def relAdnominal : Marker :=
  { form := "-(n)ɨn, -n, -l"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject, .directObject, .indirectObject, .oblique} }

/-- The adnominal clause with the possessive pronoun retained is the only way to relativize a
genitive. -/
def relGenitive : Marker :=
  { form := "-(ɨ)n + retained pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .preNominal
  , positions := {.genitive} }

/-- The Korean relative-clause markers. -/
def relMarkers : List Marker := [relAdnominal, relGenitive]

end Korean
