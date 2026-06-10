import Linglib.Features.Gender.Profile

/-!
# Dyirbal Gender
[corbett-2013] [corbett-1991] [dixon-1972]

WALS [corbett-2013] F31A codes Dyirbal as `sexBased` on the criterion
that Class I includes male humans. Corbett's 1991 monograph and Lakoff's
*Women, Fire, and Dangerous Things* (drawing on [dixon-1972]) classify
Dyirbal as non-sex-based on the broader principle that the system's
organising criteria (edibility, natural-force association) cut across
biological sex. The Corbett 1991 view is a per-Study override at
`Studies/Corbett1991.lean`.
-/

namespace Dyirbal.Gender

open Gender

/-- Dyirbal gender typology per WALS [corbett-2013]: 4-class sex-based
    semantic. The 4 classes are I (male humans + dangerous things),
    II (females + water/fire/fighting), III (edible plants), IV (residual). -/
def genderTypology : GenderProfile :=
  .fromWALS "Dyirbal" "dbl"
    (rawGenderCount := 4)
    (agreementTargets := [.attributive])
    (semanticBases := [.sex, .animacy, .shape])

theorem genderTypology_iso639 : genderTypology.iso639 = "dbl" := rfl

theorem genderTypology_name : genderTypology.name = "Dyirbal" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

end Dyirbal.Gender
