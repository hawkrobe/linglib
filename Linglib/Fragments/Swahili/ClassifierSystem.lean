import Linglib.Features.NounCategorization.Basic

/-!
# Swahili noun-categorization system
[aikhenvald-2000]

Classifier-system metadata for Swahili (ISO `swh`): Bantu noun-class
system with 15 classes and prefix-based concord.
-/

namespace Swahili

/-- Swahili Bantu noun-class system: 15-class inventory, prefix
    realization, agreement-rich. -/
def classifierSystem : NounCategorization.System :=
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
  , source := "[aikhenvald-2000]" }

end Swahili
