import Linglib.Typology.LanguageProfile

/-!
# Turkish typological profile

Aggregate WALS-style typological profile for Turkish (ISO 639-3 `tur`).
-/

namespace Fragments.Turkish

open Typology in
/-- Turkish: SOV, postpositional, agglutinative; participial RC. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "tur" "Turkish"
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .gap
        , rcPosition := .preNominal
        , lowestRelativizable := .oblique
        , notes := "Gap strategy; participial suffixes -en (SU), -dik (non-SU); "
                ++ "pre-nominal RC" }

end Fragments.Turkish
