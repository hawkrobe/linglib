import Linglib.Typology.Gender

/-!
# English Gender
@cite{corbett-2013} @cite{corbett-1991}

WALS @cite{corbett-2013} classifies English as 3-gender, sex-based,
semantic-only on the strength of the *he/she/it* pronoun distinction.
This is the more recent of Corbett's two classifications; his 1991
monograph applies a stricter controller-marking criterion that excludes
English from the gender typology. The Corbett 1991 view is a per-Study
override at `Phenomena/Gender/Studies/Corbett1991.lean`.
-/

namespace Fragments.English.Gender

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

end Fragments.English.Gender
