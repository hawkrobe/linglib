import Linglib.Typology.Gender

/-!
# English Gender
[corbett-2013] [corbett-1991]

WALS [corbett-2013] classifies English as 3-gender, sex-based,
semantic-only on the strength of the *he/she/it* pronoun distinction.
This agrees with [corbett-1991], which treats English as a
*pronominal gender system*: it has the category of gender (3 genders,
*he/she/it*), assigned on purely semantic grounds, but gender surfaces
only in personal, possessive, and reflexive pronouns.
-/

namespace English.Gender

open Typology.Gender

/-- English gender typology per WALS [corbett-2013]: 3-gender
    sex-based, semantic-only (he/she/it pronominal distinction). -/
def genderTypology : GenderProfile :=
  .fromWALS "English" "eng"
    (rawGenderCount := 3)
    (agreementTargets := [.personalPronoun])
    (semanticBases := [.sex])
    (attestedGenders := [.masculine, .feminine, .neuter])

theorem genderTypology_iso639 : genderTypology.iso639 = "eng" := rfl

theorem genderTypology_name : genderTypology.name = "English" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

end English.Gender
