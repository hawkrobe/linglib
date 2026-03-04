import Linglib.Core.Relativization.Basic

/-!
# Korean Relativization Fragment
@cite{keenan-comrie-1977}

Two relative clause markers:
- Adnominal verb suffix *-(n)ɨn, -n, -l* with gap (-case, covers SU–OBL)
- Genitive marker *-uy* (+case, covers GEN only)

Korean has no relative pronouns or complementizers. RCs are prenominal
with the verb in adnominal form. NP_rel and its case marker are
obligatorily deleted.

Data from @cite{keenan-comrie-1977} Table 1.
-/

namespace Fragments.Korean

open Core

/-- Adnominal verb suffix. The verb takes an adnominal (relative) form:
    *-(n)ɨn* (present), *-n* (past), *-l* (prospective/future).
    No relative pronoun or complementizer. NP_rel + case marker deleted.
    Prenominal RC. Covers SU, DO, IO, OBL.
    E.g., "[ _ tteonagan] saram" '[ _ left] person'. -/
def relAdnominal : RelClauseMarker :=
  { form := "-(n)ɨn, -n, -l"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .preNominal
  , positions := [.subject, .directObject, .indirectObject, .oblique]
  , notes := "Adnominal verb suffix; gap; NP_rel + case marker deleted" }

/-- Genitive construction. The possessor position is relativized using
    the genitive marker *-uy*. Prenominal RC.
    Covers GEN only. -/
def relGenitive : RelClauseMarker :=
  { form := "-uy"
  , npRel := .gap
  , bearsCaseMarking := true
  , rcPosition := .preNominal
  , positions := [.genitive]
  , notes := "Genitive marker; covers GEN only" }

/-- All Korean relative clause markers. -/
def relMarkers : List RelClauseMarker := [relAdnominal, relGenitive]

end Fragments.Korean
