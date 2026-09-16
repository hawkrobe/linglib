import Linglib.Syntax.Clause.Relative

/-!
# Japanese relative clauses

Japanese relative clauses precede their head with no relativizer and no relative pronoun. The
relativized position is normally left empty, and this relativizes subjects, direct objects and
indirect objects freely and obliques and genitives for some noun phrases; objects of comparison
are not relativized, though the paper judges the result not too bad. A pronoun may instead be
retained, and only when the relativized position is a genitive. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

namespace Japanese

open RelativeClause

/-- The unmarked prenominal clause leaves the relativized position empty and relativizes subjects
through genitives. -/
def relGap : Marker :=
  { form := "∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject, .directObject, .indirectObject, .oblique, .genitive} }

/-- The unmarked prenominal clause with a retained pronoun relativizes genitives only. -/
def relRetention : Marker :=
  { form := "∅ + pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .preNominal
  , positions := {.genitive} }

/-- The Japanese relative-clause markers. -/
def relMarkers : List Marker := [relGap, relRetention]

end Japanese
