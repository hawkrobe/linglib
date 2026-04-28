import Linglib.Core.Relativization.Basic
import Linglib.Typology.Relativization.Defs

/-!
# English Relativization Fragment
@cite{keenan-comrie-1977}

Two relative clause markers:
- Complementizer *that*/∅ with gap in NP_rel (-case, covers SU/DO)
- Relative pronoun *who/whom/which/whose* (+case, covers IO–OCOMP)

Data from @cite{keenan-comrie-1977} Table 1.
-/

namespace Fragments.English

open Core

/-- Complementizer *that* or zero (∅). NP_rel is deleted (gap).
    Covers subject and direct object relativization.
    E.g., "the man [that _ left]", "the book [∅ I read _]". -/
def relThat : RelClauseMarker :=
  { form := "that/∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject, .directObject]
  , notes := "Complementizer that or zero; NP_rel deleted" }

/-- Relative pronoun *who/whom/which/whose*. Bears case marking
    (who/whom/whose distinguish nominative/accusative/genitive).
    Covers IO–OCOMP via pied-piping.
    E.g., "the man [to whom I gave the book]",
    "the man [whose book I read _]". -/
def relWhom : RelClauseMarker :=
  { form := "who/whom/which/whose"
  , npRel := .relPronoun
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.indirectObject, .oblique, .genitive, .objComparison]
  , notes := "Relative pronoun with case (who/whom/whose); pied-piping" }

/-- All English relative clause markers. -/
def relMarkers : List RelClauseMarker := [relThat, relWhom]

/-- English relativization profile (typological summary). -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .mixed
  , oblStrategy := .mixed
  , rcPosition := .postNominal
  , lowestRelativizable := .objComparison
  , notes := "Gap + relative pronoun; P-stranding allows gap on obliques; "
          ++ "can relativize all AH positions" }

end Fragments.English
