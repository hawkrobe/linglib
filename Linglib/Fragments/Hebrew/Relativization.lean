import Linglib.Core.Relativization.Basic

/-!
# Hebrew Relativization Fragment
@cite{keenan-comrie-1977}

Two relative clause markers (discussed §1.3.2):
- Complementizer *she-* with gap (-case, covers SU/DO)
- Same *she-* with resumptive pronoun (+case, covers DO–OCOMP)

DO is shared between both constructions.

Data from @cite{keenan-comrie-1977} Table 1 and §1.3.2.
-/

namespace Fragments.Hebrew

open Core

/-- Complementizer *she-*. NP_rel is deleted (gap).
    Covers subject and direct object.
    E.g., "ha-ish [she-halakh _]" 'the-man [that-left _]'. -/
def relSheGap : RelClauseMarker :=
  { form := "she-"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject, .directObject]
  , notes := "Complementizer she-; gap; covers SU/DO; §1.3.2" }

/-- Complementizer *she-* with resumptive pronoun. Same complementizer
    introduces the RC, but NP_rel is a resumptive personal pronoun.
    Covers DO–OCOMP (DO shared with gap construction).
    E.g., "ha-ir [she-garti ba-h]" 'the-city [that-lived-I in-it]'. -/
def relSheResumptive : RelClauseMarker :=
  { form := "she- + pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.directObject, .indirectObject, .oblique, .genitive, .objComparison]
  , notes := "Complementizer she-; resumptive; DO–OCOMP; DO shared; §1.3.2" }

/-- All Hebrew relative clause markers. -/
def relMarkers : List RelClauseMarker := [relSheGap, relSheResumptive]

end Fragments.Hebrew
