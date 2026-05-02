import Linglib.Typology.Gender

/-!
# French Gender
@cite{corbett-1991} @cite{corbett-2013}

2 genders (masc/fem), sex-based, semantic + formal. Agreement on determiners,
attributive + predicate adjectives, past participles, and personal pronouns.
-/

namespace Fragments.French.Gender

open Typology.Gender
open Core (AgreementTarget)

/-- French gender typology: 2-gender canonical sex-based. -/
def genderTypology : GenderProfile :=
  .fromWALS "French" "fra"
    (rawGenderCount := 2)
    (genderCountFb := .two)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .personalPronoun])
    (semanticBases := [.sex])
    (attestedSurfaceGenders := [.masculine, .feminine])

example : genderTypology.iso639 = "fra" ∧ genderTypology.name = "French" :=
  ⟨rfl, rfl⟩

end Fragments.French.Gender
