import Linglib.Typology.LanguageProfile
import Linglib.Fragments.Korean.Morph

/-!
# Korean typological profile

Aggregate WALS-style typological profile for Korean (ISO 639-3 `kor`).
-/

namespace Fragments.Korean

open Typology in
/-- Korean: SOV, postpositional, head-final like Japanese. -/
def typology : LanguageProfile :=
  LanguageProfile.empty "kor" "Korean"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .gap
        , rcPosition := .preNominal
        , lowestRelativizable := .oblique
        , notes := "Gap strategy; pre-nominal RC; parallel to Japanese" }

end Fragments.Korean
