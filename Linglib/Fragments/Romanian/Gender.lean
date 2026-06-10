import Linglib.Morphology.Gender

/-!
# Romanian Gender
[corbett-1991] [corbett-2013]

3 genders (masc/fem/neuter — the neuter behaves as masc in the singular and
fem in the plural; "ambigeneric"). Sex-based, semantic + formal.
-/

namespace Romanian.Gender

open Morphology.Gender

/-- Romanian gender typology: 3-gender sex-based with ambigeneric neuter. -/
def genderTypology : GenderProfile :=
  .fromWALS "Romanian" "ron"
    (rawGenderCount := 3)
    (genderCountFb := .three)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .personalPronoun])
    (semanticBases := [.sex])
    (attestedGenders := [.masculine, .feminine, .neuter])

theorem genderTypology_iso639 : genderTypology.iso639 = "ron" := rfl

theorem genderTypology_name : genderTypology.name = "Romanian" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Romanian is in [corbett-1991]'s "canonical" cell. -/
theorem isCanonicalGender_genderTypology :
    genderTypology.IsCanonicalGender := by decide

end Romanian.Gender
