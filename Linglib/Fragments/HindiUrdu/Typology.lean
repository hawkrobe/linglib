import Linglib.Typology.LanguageProfile

/-!
# Hindi-Urdu typological profile

Aggregate WALS-style typological profile for Hindi-Urdu (ISO 639-3 `hin`).
-/

namespace Fragments.HindiUrdu

open Typology in
/-- Hindi-Urdu: SOV, postpositional; correlative RC strategy. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "hin" "Hindi-Urdu"
    |>.withRelativization
        { subjStrategy := .relativePronoun
        , oblStrategy := .relativePronoun
        , rcPosition := .correlative
        , lowestRelativizable := .oblique
        , notes := "Correlative jo...vo; rel pronoun jo declines; "
                ++ "post-nominal RC also possible in formal register" }

end Fragments.HindiUrdu
