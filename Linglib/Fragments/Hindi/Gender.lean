import Linglib.Typology.Gender

/-!
# Hindi-Urdu Gender
[corbett-1991] [corbett-2013]

2 genders (masc/fem). Agreement on adjectives, verbs (in perfective aspect),
and auxiliaries — one of the clearest cases of verb agreement for gender.
-/

namespace Hindi.Gender

open Typology.Gender

/-- Hindi-Urdu gender typology: 2-gender canonical sex-based with verb agr. -/
def genderTypology : GenderProfile :=
  .fromWALS "Hindi-Urdu" "hin"
    (rawGenderCount := 2)
    (agreementTargets := [.attributive, .predicate, .verb])
    (semanticBases := [.sex])
    (attestedGenders := [.masculine, .feminine])

theorem genderTypology_iso639 : genderTypology.iso639 = "hin" := rfl

theorem genderTypology_name : genderTypology.name = "Hindi-Urdu" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Hindi-Urdu is in [corbett-1991]'s "canonical" cell. -/
theorem isCanonicalGender_genderTypology :
    genderTypology.IsCanonicalGender := by decide

end Hindi.Gender
