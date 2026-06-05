import Linglib.Typology.Gender

/-!
# Swahili Gender
[corbett-1991] [corbett-2013]

7 controller genders — the singular/plural pairings 1/2, 3/4, 5/6, 7/8,
9/10, 11/10, 15 of [corbett-1991]'s Table 3.4 — over ~15 traditional
noun classes; the locative classes 16/17/18 are minor target genders,
not controller genders ([corbett-1991] §6.3.3). Semantic + formal
assignment via prefixes, with concord on all five `AgreementTarget`
positions (Swahili concord also reaches numerals, possessives, and
demonstratives, which the enum does not model). `attestedSurfaceGenders`
stays `[]`: noun-class agreement doesn't map onto the Indo-European
`SurfaceGender` scheme.
-/

namespace Swahili.Gender

open Typology.Gender

/-- Swahili gender typology: 7 controller genders (Bantu), semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Swahili" "swh"
    (rawGenderCount := 7)
    (genderCountFb := .fivePlus)
    (basisFb := .nonSexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .relativePronoun,
                          .personalPronoun, .verb])
    (semanticBases := [.humanness, .animacy, .shape])

theorem genderTypology_iso639 : genderTypology.iso639 = "swh" := rfl

theorem genderTypology_name : genderTypology.name = "Swahili" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Swahili is a noun-class system (5+ genders per [corbett-1991]). -/
theorem isNounClassSystem_genderTypology :
    genderTypology.IsNounClassSystem := by decide

end Swahili.Gender
