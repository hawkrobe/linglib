import Linglib.Core.Typology.LanguageProfile

/-!
# Hebrew (Modern) typological profile

Aggregate WALS-style typological profile for Hebrew (ISO 639-3 `heb`).
-/

namespace Fragments.Hebrew

open Core.Typology in
/-- Modern Hebrew: SVO, prepositional, complementizer-introduced RC. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "heb" "Hebrew"
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .pronounRetention
        , rcPosition := .postNominal
        , lowestRelativizable := .oblique
        , notes := "Gap on subject, resumptive on obliques; "
                ++ "complementizer she-; classic Semitic AH shift" }

end Fragments.Hebrew
