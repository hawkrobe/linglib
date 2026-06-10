import Linglib.Features.Gender.Profile

/-!
# Xhosa Gender
[corbett-1991] [corbett-2013]

Bantu noun-class system. [carstens-2026] cites 5 active genders —
controller genders 1/2, 3/4, 5/6, 7/8, 9/10 (labels A–E) — for the
agreement-side analysis; the morphological class inventory is larger.
-/

namespace Xhosa.Gender

open _root_.Gender

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

theorem genderTypology_iso639 : genderTypology.iso639 = "xho" := rfl

theorem genderTypology_name : genderTypology.name = "Xhosa" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Xhosa is a noun-class system (Bantu, 5+ classes). -/
theorem isNounClassSystem_genderTypology :
    genderTypology.IsNounClassSystem := by decide

end Xhosa.Gender
