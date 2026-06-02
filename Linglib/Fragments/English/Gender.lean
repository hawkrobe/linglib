import Linglib.Typology.Gender

/-!
# English Gender
@cite{corbett-2013} @cite{corbett-1991}

WALS @cite{corbett-2013} classifies English as 3-gender, sex-based,
semantic-only on the strength of the *he/she/it* pronoun distinction.
This agrees with @cite{corbett-1991}, which treats English as a
*pronominal gender system*: it has the category of gender (3 genders,
*he/she/it*), assigned on purely semantic grounds, but gender surfaces
only in personal, possessive, and reflexive pronouns.
-/

namespace English.Gender

open Typology.Gender

/-- English gender typology per WALS @cite{corbett-2013}: 3-gender
    sex-based, semantic-only (he/she/it pronominal distinction). -/
def genderTypology : GenderProfile :=
  .fromWALS "English" "eng"
    (rawGenderCount := 3)
    (genderCountFb := .three)
    (basisFb := .sexBased)
    (assignmentFb := .semanticOnly)
    (agreementTargets := [.personalPronoun])
    (semanticBases := [.sex])
    (attestedSurfaceGenders := [.masculine, .feminine, .neuter])

example : genderTypology.iso639 = "eng" ∧ genderTypology.name = "English" :=
  ⟨rfl, rfl⟩

end English.Gender
