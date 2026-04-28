import Linglib.Typology.LanguageProfile

/-!
# Yoruba typological profile
@cite{awobuluyi-1978} @cite{ajiboye-2005}

Aggregate WALS-style typological profile for Yoruba (ISO 639-3 `yor`).
SVO and prepositional facts are inherited from WALS via `ofWALS`. The
relativization profile is hand-coded from @cite{awobuluyi-1978} §6.18–6.23
(the work WALS itself cites for F122A); per-marker breakdown lives in
`Fragments.Yoruba.Relativization`. @cite{ajiboye-2005} provides theoretical
backing for the C-head / introducer analysis of `tí` (§1.2.2 reduced
relatives in genitive DPs) and head-initial Yorùbá DP structure (§1.2.3.2).
-/

namespace Fragments.Yoruba

open Typology in
/-- Yoruba: SVO, prepositional. Relativization uses the introducer `tí`
    (high tone), with strategy varying by Accessibility-Hierarchy position. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "yor" "Yoruba"
    |>.withRelativization
        { subjStrategy := .pronounRetention
        , oblStrategy := .gap
        , rcPosition := .postNominal
        , lowestRelativizable := .genitive
        , internallyHeaded := .absent
        , notes := "Relativizer tí (high tone; distinct from preverbal/preposition ti). "
                ++ "@cite{awobuluyi-1978} §6.19 SU resumption (ó); §6.20 DO gap; "
                ++ "§6.21 OBL gap (fi/ti/bá/fún/sí); §6.22 OBL with ní triggers "
                ++ "drop+repositioning (complexity not captured by oblStrategy field); "
                ++ "§6.23 GEN resumption (rẹ̀ sg / wọn pl). "
                ++ "Per-position markers in Fragments.Yoruba.relMarkers. "
                ++ "Awobuluyi §6.24 rejects relative-pronoun analysis of tí." }

end Fragments.Yoruba
