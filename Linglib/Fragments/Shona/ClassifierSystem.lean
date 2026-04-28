import Linglib.Typology.ClassifierSystem

/-!
# Shona noun-categorization system
@cite{carstens-2026}

Classifier-system metadata for Shona (ISO `sna`): Bantu noun-class
system with 14 classes and binary human/non-human split.
-/

namespace Fragments.Shona

/-- Shona Bantu noun-class system: 14-class inventory, prefix
    realization, agreement-rich. -/
def classifierSystem : Typology.NounCategorizationSystem :=
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
