import Linglib.Typology.Gender

/-!
# Xhosa Gender
[corbett-1991] [corbett-2013]

Bantu noun-class system. Carstens 2026 cites 5 active gender classes for
the agreement-side analysis; the morphological inventory is larger.
-/

namespace Xhosa.Gender

open Typology.Gender

/-- Xhosa gender typology: noun-class Bantu, semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Xhosa" "xho"
    (rawGenderCount := 5)
    (genderCountFb := .fivePlus)
    (basisFb := .nonSexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .relativePronoun,
                          .personalPronoun, .verb])
    (semanticBases := [.humanness, .animacy])

example : genderTypology.iso639 = "xho" ∧ genderTypology.name = "Xhosa" :=
  ⟨rfl, rfl⟩

/-- Xhosa is a noun-class system (Bantu, 5+ classes). -/
example : genderTypology.IsNounClassSystem := by decide

end Xhosa.Gender
