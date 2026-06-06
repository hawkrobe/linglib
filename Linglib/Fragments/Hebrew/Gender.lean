import Linglib.Typology.Gender

/-!
# Hebrew Gender
[corbett-1991] [corbett-2013]

2 genders (masc/fem), sex-based, semantic + formal. Verb agreement in person
+ number + gender (the clearest Semitic case of verbal gender agreement).
-/

namespace Hebrew.Gender

open Typology.Gender

/-- Hebrew gender typology: 2-gender canonical sex-based with verb agreement. -/
def genderTypology : GenderProfile :=
  .fromWALS "Hebrew" "heb"
    (rawGenderCount := 2)
    (agreementTargets := [.attributive, .predicate, .verb])
    (semanticBases := [.sex])
    (attestedGenders := [.masculine, .feminine])

theorem genderTypology_iso639 : genderTypology.iso639 = "heb" := rfl

theorem genderTypology_name : genderTypology.name = "Hebrew" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Hebrew is in [corbett-1991]'s "canonical" cell. -/
theorem isCanonicalGender_genderTypology :
    genderTypology.IsCanonicalGender := by decide

end Hebrew.Gender
