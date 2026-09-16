import Linglib.Syntax.RelativeClause.Basic

/-!
# Korean relative-clause markers

The Korean relativization strategies as [keenan-comrie-1977] records them (Section 1.3.4 and
Table 1): a prenominal clause whose verb carries the adnominal suffix, the relativized position
deleted, from subject through oblique; and the same prenominal clause with a retained pronoun in
the relativized position for genitives. Korean has no relative pronoun or complementizer.

## References

* [keenan-comrie-1977]
-/

namespace Korean

open RelativeClause

/-- Adnominal verb suffix. The verb takes an adnominal (relative) form:
    *-(n)ɨn* (present), *-n* (past), *-l* (prospective/future).
    No relative pronoun or complementizer. NP_rel + case marker deleted.
    Prenominal RC. Covers SU, DO, IO, OBL.
    E.g., "[ _ tteonagan] saram" '[ _ left] person'. -/
def relAdnominal : Marker :=
  { form := "-(n)ɨn, -n, -l"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject, .directObject, .indirectObject, .oblique} }

/-- The adnominal clause with a retained pronoun in the relativized position, the strategy
genitives require: [keenan-comrie-1977]'s (25), *chaki-ij lä-ka chongmyəngha-n kɨ salam* 'the man
whose dog is smart', with the possessive pronoun *chaki-ij* 'his' retained. -/
def relGenitive : Marker :=
  { form := "-(ɨ)n + retained pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .preNominal
  , positions := {.genitive} }

/-- All Korean relative clause markers. -/
def relMarkers : List Marker := [relAdnominal, relGenitive]

end Korean
