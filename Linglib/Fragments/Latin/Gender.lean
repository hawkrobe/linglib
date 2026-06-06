import Linglib.Typology.Gender

/-!
# Latin Gender
[corbett-1991] [corbett-2013]

3 genders (masc/fem/neut), sex-based, semantic + formal. Agreement on
attributive + predicate adjectives, relative + personal pronouns.
-/

namespace Latin.Gender

open Typology.Gender

/-- Latin gender typology: 3-gender canonical sex-based. -/
def genderTypology : GenderProfile :=
  .fromWALS "Latin" "lat"
    (rawGenderCount := 3)
    (genderCountFb := .three)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun])
    (semanticBases := [.sex])
    (attestedGenders := [.masculine, .feminine, .neuter])

theorem genderTypology_iso639 : genderTypology.iso639 = "lat" := rfl

theorem genderTypology_name : genderTypology.name = "Latin" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Latin is in [corbett-1991]'s "canonical" cell. -/
theorem isCanonicalGender_genderTypology :
    genderTypology.IsCanonicalGender := by decide

end Latin.Gender
