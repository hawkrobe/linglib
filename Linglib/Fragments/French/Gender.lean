import Linglib.Typology.Gender

/-!
# French Gender
@cite{corbett-1991} @cite{corbett-2013}

2 genders (masc/fem), sex-based, semantic + formal. Agreement on determiners,
attributive + predicate adjectives, past participles, and personal pronouns.
-/

namespace French.Gender

open Typology.Gender

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

/-- French is in @cite{corbett-1991}'s "canonical" cell:
    sex-based, 2-or-3 gender, semantic + formal. -/
example : genderTypology.IsCanonicalGender := by decide

end French.Gender
