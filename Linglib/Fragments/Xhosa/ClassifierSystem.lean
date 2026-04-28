import Linglib.Typology.ClassifierSystem

/-!
# Xhosa noun-categorization system
@cite{carstens-2026} @cite{taraldsen-et-al-2018}

Classifier-system metadata for Xhosa (ISO `xho`): Bantu noun-class
system with 11 classes and pervasive concord.
-/

namespace Fragments.Xhosa

/-- Xhosa Bantu noun-class system: 11-class inventory, prefix
    realization, agreement-rich. -/
def classifierSystem : Typology.NounCategorizationSystem :=
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
