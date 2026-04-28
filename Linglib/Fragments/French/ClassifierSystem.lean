import Linglib.Typology.ClassifierSystem

/-!
# French noun-categorization system
@cite{aikhenvald-2000}

Classifier-system data for French (ISO `fra`): masculine/feminine
noun-class system per @cite{aikhenvald-2000} §2.
-/

namespace Fragments.French

/-- French noun-class system: 2-class gender (masculine/feminine),
    obligatory agreement, mostly semantic + morphological residue. -/
def classifierSystem : Typology.NounCategorizationSystem :=
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
