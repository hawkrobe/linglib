import Linglib.Syntax.RelativeClause.Basic
import Linglib.Syntax.RelativeClause.WALS

/-!
# Korean Relativization Fragment
[keenan-comrie-1977]

Two relative clause markers:
- Adnominal verb suffix *-(n)ɨn, -n, -l* with gap (-case, covers SU–OBL)
- Genitive marker *-uy* (+case, covers GEN only)

Korean has no relative pronouns or complementizers. RCs are prenominal
with the verb in adnominal form. NP_rel and its case marker are
obligatorily deleted.

Data from [keenan-comrie-1977] Table 1.
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
  , rcPosition := .preNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique]
  , notes := "Adnominal verb suffix; gap; NP_rel + case marker deleted" }

/-- Genitive construction. The possessor position is relativized using
    the genitive marker *-uy*. Prenominal RC.
    Covers GEN only. -/
def relGenitive : Marker :=
  { form := "-uy"
  , npRel := .gap
  , bearsCaseMarking := true
  , rcPosition := .preNominal
  , positions := [.genitive]
  , notes := "Genitive marker; covers GEN only" }

/-- All Korean relative clause markers. -/
def relMarkers : List Marker := [relAdnominal, relGenitive]

/-- Korean relativization profile (typological summary). -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .gap
  , oblStrategy := .gap
  , rcPosition := .preNominal
  , lowestRelativizable := .oblique
  , notes := "Gap strategy; pre-nominal RC; parallel to Japanese" }

end Korean
