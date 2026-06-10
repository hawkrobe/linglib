import Linglib.Features.Gender.Profile

/-!
# Fula Gender
[corbett-1991] [corbett-2013]

"About twenty genders, depending on the dialect" ([corbett-1991] §7.1.1)
— one of the richest gender systems in Africa (Atlantic, Niger-Congo).
Sample maximum in Corbett's 22-language exemplar.
-/

namespace Fula.Gender

open _root_.Gender

/-- Fula gender typology: ~20 genders (Atlantic), semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Fula" "ful"
    (rawGenderCount := 20)
    (genderCountFb := .fivePlus)
    (basisFb := .nonSexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .personalPronoun, .verb])
    (semanticBases := [.humanness, .animacy, .shape])

theorem genderTypology_iso639 : genderTypology.iso639 = "ful" := rfl

theorem genderTypology_name : genderTypology.name = "Fula" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Fula is a noun-class system (~20 genders per [corbett-1991]). -/
theorem isNounClassSystem_genderTypology :
    genderTypology.IsNounClassSystem := by decide

end Fula.Gender
