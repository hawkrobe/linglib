import Linglib.Syntax.RelativeClause.Basic

/-!
# Russian Relativization Fragment
[keenan-comrie-1977]

One relative clause marker: the declining relative pronoun *kotoryj*
(+case, postnominal, covers SU–GEN; Table 1 leaves OCOMP blank).
§1.3.1 also mentions a subjects-only participial strategy for Russian
(alongside German and Polish), but Table 1 does not enter it, so it is
not encoded here.

Data from [keenan-comrie-1977] Table 1.
-/

namespace Russian

open RelativeClause

/-- Declining relative pronoun *kotoryj*; postnominal RC. Covers SU–GEN
    (Table 1 p. 78; OCOMP blank). "The RC construction is essentially as
    in Polish, the relative pronoun being *kotoryj*"
    ([keenan-comrie-1979] p. 344, exx. (87)-(88)). -/
def relKotoryj : Marker :=
  { form := "kotoryj"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique, .genitive]
  , notes := "Declining relative pronoun; OCOMP no data" }

/-- All Russian relative clause markers. -/
def relMarkers : List Marker := [relKotoryj]

end Russian
