import Linglib.Typology.LanguageProfile

/-!
# Italian typological profile

Aggregate WALS-style typological profile for Italian (ISO 639-3 `ita`).
-/

namespace Fragments.Italian

open Typology in
/-- Italian: SVO, prepositional, 2-class gender system (masc/fem). -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "ita" "Italian"
    |>.withClassifierSystem
        { family := "Indo-European"
        , classifierType := .nounClass
        , scopes := [.headModifierNP, .predicateArgument]
        , assignment := .mixed  -- semantic (sex) + morphological (-o/-a endings)
        , realizations := [.freeForm, .suffix]  -- il/la + -o/-a, etc.
        , hasAgreement := true
        , inventorySize := 2  -- masculine, feminine
        , isObligatory := true
        , hasUnmarkedDefault := true  -- masculine is unmarked
        , preferredSemantics := [.sex, .animacy]
        , hasObligatoryNumber := true  -- il/i, la/le, un/una
        , source := "@cite{aikhenvald-2000} §2; @cite{chierchia-1998}" }

end Fragments.Italian
