import Linglib.Core.Typology.LanguageProfile
import Linglib.Fragments.Arabic.Morph

/-!
# Arabic (Modern Standard) typological profile

Aggregate WALS-style typological profile for MSA (ISO 639-3 `arb`).
-/

namespace Fragments.Arabic

open Core.Typology in
/-- MSA: VSO, prepositional. -/
def typology : LanguageProfile :=
  LanguageProfile.empty "arb" "Arabic (MSA)"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile
    |>.withRelativization
        { subjStrategy := .mixed
        , oblStrategy := .pronounRetention
        , rcPosition := .postNominal
        , lowestRelativizable := .oblique
        , notes := "Gap on subject, resumptive on obliques; classic AH shift; "
                ++ "complementizer alladhi/allati" }

end Fragments.Arabic
