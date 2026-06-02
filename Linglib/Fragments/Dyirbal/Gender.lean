import Linglib.Typology.Gender

/-!
# Dyirbal Gender
@cite{corbett-2013} @cite{corbett-1991} @cite{dixon-1972}

WALS @cite{corbett-2013} F31A codes Dyirbal as `sexBased` on the criterion
that Class I includes male humans. Corbett's 1991 monograph and Lakoff's
*Women, Fire, and Dangerous Things* (drawing on @cite{dixon-1972}) classify
Dyirbal as non-sex-based on the broader principle that the system's
organising criteria (edibility, natural-force association) cut across
biological sex. The Corbett 1991 view is a per-Study override at
`Studies/Corbett1991.lean`.
-/

namespace Dyirbal.Gender

open Typology.Gender

/-- Dyirbal gender typology per WALS @cite{corbett-2013}: 4-class sex-based
    semantic. The 4 classes are I (male humans + dangerous things),
    II (females + water/fire/fighting), III (edible plants), IV (residual). -/
def genderTypology : GenderProfile :=
  .fromWALS "Dyirbal" "dbl"
    (rawGenderCount := 4)
    (genderCountFb := .four)
    (basisFb := .sexBased)
    (assignmentFb := .semanticOnly)
    (agreementTargets := [.attributive])
    (semanticBases := [.sex, .animacy, .shape])

example : genderTypology.iso639 = "dbl" ∧ genderTypology.name = "Dyirbal" :=
  ⟨rfl, rfl⟩

end Dyirbal.Gender
