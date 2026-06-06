import Linglib.Typology.Gender

/-!
# Irish Gender
[corbett-1991] [corbett-2013]

2 genders (masc/fem), sex-based, semantic + formal. Agreement on attributive
adjectives and personal pronouns; no predicate adjective agreement (unlike
Romance).
-/

namespace Irish.Gender

open Typology.Gender

/-- Irish gender typology: 2-gender sex-based, restricted agreement targets. -/
def genderTypology : GenderProfile :=
  .fromWALS "Irish" "gle"
    (rawGenderCount := 2)
    (genderCountFb := .two)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .personalPronoun])
    (semanticBases := [.sex])
    (attestedGenders := [.masculine, .feminine])

theorem genderTypology_iso639 : genderTypology.iso639 = "gle" := rfl

theorem genderTypology_name : genderTypology.name = "Irish" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Irish is in [corbett-1991]'s "canonical" cell. -/
theorem isCanonicalGender_genderTypology :
    genderTypology.IsCanonicalGender := by decide

end Irish.Gender
