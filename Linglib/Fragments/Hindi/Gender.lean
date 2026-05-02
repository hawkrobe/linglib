import Linglib.Typology.Gender

/-!
# Hindi-Urdu Gender
@cite{corbett-1991} @cite{corbett-2013}

2 genders (masc/fem). Agreement on adjectives, verbs (in perfective aspect),
and auxiliaries — one of the clearest cases of verb agreement for gender.
-/

namespace Fragments.Hindi.Gender

open Typology.Gender

/-- Hindi-Urdu gender typology: 2-gender canonical sex-based with verb agr. -/
def genderTypology : GenderProfile :=
  .fromWALS "Hindi-Urdu" "hin"
    (rawGenderCount := 2)
    (genderCountFb := .two)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .verb])
    (semanticBases := [.sex])
    (attestedSurfaceGenders := [.masculine, .feminine])

example : genderTypology.iso639 = "hin" ∧ genderTypology.name = "Hindi-Urdu" :=
  ⟨rfl, rfl⟩

/-- Hindi-Urdu is in @cite{corbett-1991}'s "canonical" cell. -/
example : genderTypology.IsCanonicalGender := by decide

end Fragments.Hindi.Gender
