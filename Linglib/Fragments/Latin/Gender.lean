import Linglib.Typology.Gender

/-!
# Latin Gender
@cite{corbett-1991} @cite{corbett-2013}

3 genders (masc/fem/neut), sex-based, semantic + formal. Agreement on
attributive + predicate adjectives, relative + personal pronouns.
-/

namespace Fragments.Latin.Gender

open Typology.Gender
open Core (AgreementTarget)

/-- Latin gender typology: 3-gender canonical sex-based. -/
def genderTypology : GenderProfile :=
  .fromWALS "Latin" "lat"
    (rawGenderCount := 3)
    (genderCountFb := .three)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun])
    (semanticBases := [.sex])
    (attestedSurfaceGenders := [.masculine, .feminine, .neuter])

example : genderTypology.iso639 = "lat" ∧ genderTypology.name = "Latin" := ⟨rfl, rfl⟩

end Fragments.Latin.Gender
