import Linglib.Core.Relativization.Basic
import Linglib.Typology.Relativization.Defs

/-!
# Toba Batak Relativization Fragment
@cite{keenan-comrie-1977}

Two relative clause markers (discussed §1.3.2):
- Gap construction (-case, covers SU only)
- Resumptive pronoun (+case, covers IO/OBL/GEN)

DO cannot be relativized by either construction — a genuine gap in
AH coverage, noted explicitly in the paper.

Data from @cite{keenan-comrie-1977} Table 1 and §1.3.2.
-/

namespace Fragments.TobaBatak

open Core

/-- Gap construction. NP_rel is deleted. Postnominal RC.
    Covers subject only.
    The -case strategy is maximally restricted (like Arabic). -/
def relGap : RelClauseMarker :=
  { form := "∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject]
  , notes := "Gap; SU only; §1.3.2" }

/-- Resumptive pronoun construction. NP_rel is a pronominal copy
    bearing case. Postnominal RC. Covers IO, OBL, GEN.
    Crucially does NOT cover DO — neither strategy can relativize
    direct objects in Toba Batak. -/
def relResumptive : RelClauseMarker :=
  { form := "pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.indirectObject, .oblique, .genitive]
  , notes := "Resumptive; IO/OBL/GEN; DO gap genuine; §1.3.2" }

/-- All Toba Batak relative clause markers. -/
def relMarkers : List RelClauseMarker := [relGap, relResumptive]

/-- Toba Batak relativization profile (typological summary). The
    `subjStrategy = .gap` + `oblStrategy = .pronounRetention` pair is
    K&C's canonical "DO-gap-with-resumptive-elsewhere" datapoint; DO is
    a genuine gap in AH coverage (neither strategy can relativize it). -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .pronounRetention
  , rcPosition := .postNominal
  , lowestRelativizable := .genitive
  , notes := "Gap on subject; resumptive on IO/OBL/GEN; "
          ++ "DO genuinely cannot be relativized; @cite{keenan-comrie-1977} §1.3.2" }

end Fragments.TobaBatak
