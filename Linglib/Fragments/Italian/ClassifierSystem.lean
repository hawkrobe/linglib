import Linglib.Features.NounCategorization.Basic

/-!
# Italian noun-categorization system
[aikhenvald-2000] [chierchia-1998]

Classifier-system data for Italian (ISO `ita`): 2-class gender system
(masculine/feminine).
-/

namespace Italian

/-- Italian noun-class system: 2-class gender (masculine/feminine);
    semantic (sex) + morphological (-o / -a endings) assignment. -/
def classifierSystem : NounCategorization.System :=
  { family := "Indo-European"
  , classifierType := .nounClass
  , scopes := [.headModifierNP, .predicateArgument]
  , assignment := .mixed  -- semantic (sex) + morphological (-o / -a endings)
  , realizations := [.freeForm, .suffix]  -- il/la + -o/-a, etc.
  , hasAgreement := true
  , inventorySize := 2  -- masculine, feminine
  , isObligatory := true
  , hasUnmarkedDefault := true  -- masculine is unmarked
  , preferredSemantics := [.sex, .animacy]
  , hasObligatoryNumber := true  -- il/i, la/le, un/una
  , source := "[aikhenvald-2000] §2; [chierchia-1998]" }

end Italian
