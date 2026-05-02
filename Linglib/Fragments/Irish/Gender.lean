import Linglib.Typology.Gender

/-!
# Irish Gender
@cite{corbett-1991} @cite{corbett-2013}

2 genders (masc/fem), sex-based, semantic + formal. Agreement on attributive
adjectives and personal pronouns; no predicate adjective agreement (unlike
Romance).
-/

namespace Fragments.Irish.Gender

open Typology.Gender

/-- Irish gender typology: 2-gender sex-based, restricted agreement targets. -/
def genderTypology : GenderProfile :=
  .fromWALS "Irish" "gle"
    (rawGenderCount := 2)
    (genderCountFb := .two)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .personalPronoun])
    (semanticBases := [.sex])
    (attestedSurfaceGenders := [.masculine, .feminine])

example : genderTypology.iso639 = "gle" ∧ genderTypology.name = "Irish" :=
  ⟨rfl, rfl⟩

/-- Irish is in @cite{corbett-1991}'s "canonical" cell. -/
example : genderTypology.IsCanonicalGender := by decide

end Fragments.Irish.Gender
