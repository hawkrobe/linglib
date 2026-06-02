import Linglib.Typology.Gender

/-!
# Zulu Gender
[corbett-1991] [corbett-2013]

~15 noun classes. Bantu noun-class system parallel to Swahili.
-/

namespace Zulu.Gender

open Typology.Gender

/-- Zulu gender typology: 15-class Bantu, semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Zulu" "zul"
    (rawGenderCount := 15)
    (genderCountFb := .fivePlus)
    (basisFb := .nonSexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .relativePronoun,
                          .personalPronoun, .verb])
    (semanticBases := [.humanness, .animacy, .shape])

example : genderTypology.iso639 = "zul" ∧ genderTypology.name = "Zulu" :=
  ⟨rfl, rfl⟩

/-- Zulu is a noun-class system (5+ classes per [corbett-1991]). -/
example : genderTypology.IsNounClassSystem := by decide

end Zulu.Gender
