import Linglib.Core.Typology.LanguageProfile

/-!
# Shona typological profile

Aggregate WALS-style typological profile for Shona (ISO 639-3 `sna`).
-/

namespace Fragments.Shona

open Core.Typology in
/-- Shona: Bantu, 14-class noun-class system, binary human/non-human split. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "sna" "Shona"
    |>.withClassifierSystem
        { family := "Bantu"
        , classifierType := .nounClass
        , scopes := [.headModifierNP, .predicateArgument]
        , assignment := .mixed
        , realizations := [.prefix]
        , hasAgreement := true
        , inventorySize := 14  -- cl1-cl14
        , isObligatory := true
        , hasUnmarkedDefault := true
        , preferredSemantics := [.humanness, .animacy]
        , hasObligatoryNumber := true  -- singular/plural class pairs
        , source := "@cite{carstens-2026}" }

end Fragments.Shona
