import Linglib.Core.Typology.LanguageProfile

/-!
# Xhosa typological profile

Aggregate WALS-style typological profile for Xhosa (ISO 639-3 `xho`).
-/

namespace Fragments.Xhosa

open Core.Typology in
/-- Xhosa: Bantu, 11-class noun-class system, agreement-rich. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "xho" "Xhosa"
    |>.withClassifierSystem
        { family := "Bantu"
        , classifierType := .nounClass
        , scopes := [.headModifierNP, .predicateArgument]
        , assignment := .mixed
        , realizations := [.prefix]
        , hasAgreement := true
        , inventorySize := 11  -- cl1-cl10 + cl15
        , isObligatory := true
        , hasUnmarkedDefault := true  -- class 2 ba- / class 8 zi- as defaults
        , preferredSemantics := [.humanness, .animacy]
        , hasObligatoryNumber := true  -- singular/plural class pairs (e.g. cl1/cl2)
        , source := "@cite{carstens-2026}; @cite{taraldsen-et-al-2018}" }

end Fragments.Xhosa
