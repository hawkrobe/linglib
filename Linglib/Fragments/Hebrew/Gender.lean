import Linglib.Typology.Gender

/-!
# Hebrew Gender
@cite{corbett-1991} @cite{corbett-2013}

2 genders (masc/fem), sex-based, semantic + formal. Verb agreement in person
+ number + gender (the clearest Semitic case of verbal gender agreement).
-/

namespace Fragments.Hebrew.Gender

open Typology.Gender
open Core (AgreementTarget)

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

end Fragments.Hebrew.Gender
