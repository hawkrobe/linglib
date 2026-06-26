import Linglib.Features.NounCategorization.Basic

/-!
# Shona noun-categorization system
[carstens-2026]

Classifier-system metadata for Shona (ISO `sna`): Bantu noun-class
system with 14 classes and binary human/non-human split.
-/

namespace Shona

/-- Shona Bantu noun-class system: 14-class inventory, prefix
    realization, agreement-rich. -/
def classifierSystem : NounCategorization.System :=
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
  , source := "[carstens-2026]" }

end Shona
