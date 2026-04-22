import Linglib.Core.Typology.LanguageProfile

/-!
# Yoruba typological profile

Aggregate WALS-style typological profile for Yoruba (ISO 639-3 `yor`).
-/

namespace Fragments.Yoruba

open Core.Typology in
/-- Yoruba: SVO, prepositional; complementizer-marked RC. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "yor" "Yoruba"
    |>.withRelativization
        { subjStrategy := .mixed
        , oblStrategy := .pronounRetention
        , rcPosition := .postNominal
        , lowestRelativizable := .oblique
        , notes := "Mixed on subject (gap + retention); resumptive on obliques; "
                ++ "complementizer ti; Niger-Congo" }

end Fragments.Yoruba
