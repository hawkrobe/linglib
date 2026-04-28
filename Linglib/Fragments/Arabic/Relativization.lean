import Linglib.Core.Relativization.Basic
import Linglib.Typology.Relativization.Defs

/-!
# Arabic (Classical) Relativization Fragment
@cite{keenan-comrie-1977}

Two relative clause markers (discussed §1.3.2):
- Complementizer *alladhī/allatī* with gap (-case, covers SU only)
- Same complementizer with resumptive pronoun (+case, covers DO–OCOMP)

Data from @cite{keenan-comrie-1977} Table 1 and §1.3.2.
-/

namespace Fragments.Arabic

open Core

/-- Complementizer *alladhī* (masc.) / *allatī* (fem.). Agrees in
    gender and number with the head noun. NP_rel is deleted (gap).
    Covers subject only — the -case strategy is maximally restricted.
    E.g., "ar-rajul [alladhī ghadara _]" 'the-man [who left _]'. -/
def relAlladhi : RelClauseMarker :=
  { form := "alladhī/allatī"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject]
  , notes := "Complementizer agrees in gender/number; gap; SU only; §1.3.2" }

/-- Resumptive pronoun construction. Same complementizer *alladhī/allatī*
    introduces the RC, but NP_rel is a resumptive personal pronoun bearing
    case. Covers DO–OCOMP.
    E.g., "al-madina [allatī saafartu ila-ha]"
    'the-city [that I-traveled to-it]'. -/
def relResumptive : RelClauseMarker :=
  { form := "alladhī/allatī + pronoun"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.directObject, .indirectObject, .oblique, .genitive, .objComparison]
  , notes := "Same complementizer; resumptive pronoun in NP_rel; §1.3.2" }

/-- All Arabic (Classical) relative clause markers. -/
def relMarkers : List RelClauseMarker := [relAlladhi, relResumptive]

/-- Arabic relativization profile (typological summary). Subject strategy
    `.mixed` reflects the gap-on-SU + resumptive-on-DO split: WALS Ch 122
    has no `.mixed` category, so this entry is excluded from
    `Phenomena/Relativization/Typology.lean`'s WALS-grounding sample. -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .mixed
  , oblStrategy := .pronounRetention
  , rcPosition := .postNominal
  , lowestRelativizable := .oblique
  , notes := "Gap on subject, resumptive on obliques; classic AH shift; "
          ++ "complementizer alladhi/allati" }

end Fragments.Arabic
