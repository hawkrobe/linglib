import Linglib.Features.Gender.Profile

/-!
# Shona Gender
[corbett-1991] [corbett-2013]

Bantu noun-class system. [carstens-2026] cites 8 active genders
(controller genders); only 1/2 and 7/8 are interpretable.
-/

namespace Shona.Gender

open _root_.Gender

/-- Shona gender typology: noun-class Bantu, semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Shona" "sna"
    (rawGenderCount := 8)
    (agreementTargets := [.attributive, .predicate, .relativePronoun,
                          .personalPronoun, .verb])
    (semanticBases := [.humanness])

theorem genderTypology_iso639 : genderTypology.iso639 = "sna" := rfl

theorem genderTypology_name : genderTypology.name = "Shona" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Shona is a noun-class system (Bantu, 8 genders per [carstens-2026]). -/
theorem isNounClassSystem_genderTypology :
    genderTypology.IsNounClassSystem := by decide

end Shona.Gender
