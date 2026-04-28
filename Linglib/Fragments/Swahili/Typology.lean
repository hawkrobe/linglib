import Linglib.Typology.LanguageProfile

/-!
# Swahili typological profile

Aggregate WALS-style typological profile for Swahili (ISO 639-3 `swh`).
-/

namespace Fragments.Swahili

open Typology in
/-- Swahili: SVO, prepositional; noun-class agreement on relative marker. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "swh" "Swahili"
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .pronounRetention
        , rcPosition := .postNominal
        , lowestRelativizable := .oblique
        , notes := "Gap on subjects (with amba-); resumptive on obliques; "
                ++ "relative marker agrees in noun class" }
    |>.withClassifierSystem
        { family := "Bantu"
        , classifierType := .nounClass
        , scopes := [.headModifierNP, .predicateArgument]
        , assignment := .mixed
        , realizations := [.prefix]
        , hasAgreement := true
        , inventorySize := 15  -- cl1-cl10, cl14-cl18
        , isObligatory := true
        , hasUnmarkedDefault := true
        , preferredSemantics := [.humanness, .animacy]
        , hasObligatoryNumber := true  -- singular/plural class pairs (M/Wa, Ki/Vi, etc.)
        , source := "@cite{aikhenvald-2000}" }

end Fragments.Swahili
