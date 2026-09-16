import Linglib.Syntax.Clause.Relative

/-!
# Mandarin relative clauses

Mandarin relative clauses precede their head and end in the particle *de*. The relativized
position may be left empty, which relativizes subjects and direct objects, or filled by a
personal pronoun, which relativizes everything from direct objects down to objects of
comparison; the two overlap at direct objects, where retention is optional. Mandarin is the
sample's only prenominal-clause language whose pronoun-retention strategy reaches the bottom of
the hierarchy. The data are [keenan-comrie-1977]'s, whose Table 1 lists the language as
Chinese (spoken Pekingese).

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

namespace Mandarin

open RelativeClause

/-- The prenominal *de*-clause with the relativized position left empty relativizes subjects and
direct objects. -/
def relDeGap : Marker :=
  { form := "de"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject, .directObject} }

/-- The prenominal *de*-clause with a retained pronoun relativizes everything from direct objects
down. -/
def relDeResumptive : Marker :=
  { form := "de"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , placement := .preNominal
  , positions := {.directObject, .indirectObject, .oblique, .genitive, .objComparison} }

/-- The Mandarin relative-clause markers. -/
def relMarkers : List Marker := [relDeGap, relDeResumptive]

end Mandarin
