import Linglib.Syntax.Clause.Relative

/-!
# Tagalog relative clauses

Tagalog relativizes only the subject, the *ang*-phrase, so any other noun phrase is first
promoted to subject by the voice system. The clause is joined to its head by the linker *na*,
*-ng* after a vowel, with the relativized position left empty, and it may follow or precede the
head. The paper counts Tagalog among its subjects-only languages on the assumption that the
focus noun phrase is the subject, an assumption it discusses against Schachter's objections.
The data are [keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
* [keenan-comrie-1979]
* [schachter-otanes-1972]
-/

namespace Tagalog

open RelativeClause

/-- The postnominal clause joined by the linker *na ~ -ng* relativizes subjects only. -/
def relLinkerPost : Marker :=
  { form := "na/-ng"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .postNominal
  , positions := {.subject} }

/-- The prenominal clause joined by the linker *na ~ -ng* relativizes subjects only. -/
def relLinkerPre : Marker :=
  { form := "na/-ng"
  , npRel := .gap
  , bearsCaseMarking := false
  , placement := .preNominal
  , positions := {.subject} }

/-- The Tagalog relative-clause markers. -/
def relMarkers : List Marker := [relLinkerPost, relLinkerPre]

end Tagalog
