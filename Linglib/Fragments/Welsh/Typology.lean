import Linglib.Typology.LanguageProfile

/-!
# Welsh typological profile

Aggregate WALS-style typological profile for Welsh (ISO 639-3 `cym`).
-/

namespace Fragments.Welsh

open Typology in
/-- Welsh: VSO, prepositional; particle-marked RC. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "cym" "Welsh"
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .pronounRetention
        , rcPosition := .postNominal
        , lowestRelativizable := .oblique
        , notes := "Gap on subject (particle a); resumptive on obliques; "
                ++ "VSO language with post-nominal RC" }

end Fragments.Welsh
