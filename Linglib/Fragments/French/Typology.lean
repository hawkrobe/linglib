import Linglib.Typology.LanguageProfile

/-!
# French typological profile

Aggregate WALS-style typological profile for French (ISO 639-3 `fra`).
-/

namespace Fragments.French

open Typology in
/-- French: SVO, prepositional, declined relative pronoun system. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "fra" "French"
    |>.withRelativization
        { subjStrategy := .relativePronoun
        , oblStrategy := .relativePronoun
        , rcPosition := .postNominal
        , lowestRelativizable := .objComparison
        , notes := "Rel pronoun system: qui (SU), que (DO), dont (GEN), "
                ++ "lequel (OBL); all AH positions" }
    |>.withClassifierSystem
        { family := "Indo-European"
        , classifierType := .nounClass
        , scopes := [.headModifierNP, .predicateArgument]
        , assignment := .mixed  -- mostly semantic + morphological residue
        , realizations := [.freeForm, .suffix]  -- le/la + -e/-eur, etc.
        , hasAgreement := true
        , inventorySize := 2  -- masculine, feminine
        , isObligatory := true
        , hasUnmarkedDefault := true  -- masculine is unmarked
        , preferredSemantics := [.sex, .animacy]
        , hasObligatoryNumber := true  -- le/les, un/des
        , source := "@cite{aikhenvald-2000} §2" }

end Fragments.French
