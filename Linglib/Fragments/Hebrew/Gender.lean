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
    (genderCountFb := .two)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .verb])
    (semanticBases := [.sex])
    (attestedSurfaceGenders := [.masculine, .feminine])

example : genderTypology.iso639 = "heb" ∧ genderTypology.name = "Hebrew" :=
  ⟨rfl, rfl⟩

/-- Hebrew is in [corbett-1991]'s "canonical" cell. -/
example : genderTypology.IsCanonicalGender := by decide

end Hebrew.Gender
