import Linglib.Features.Gender.Profile

/-!
# Finnish Gender
[corbett-1991] [corbett-2013]

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Finnish.Gender

open Gender

/-- Finnish gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Finnish" "fin"
    (rawGenderCount := 0)

theorem genderTypology_iso639 : genderTypology.iso639 = "fin" := rfl

theorem genderTypology_name : genderTypology.name = "Finnish" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

end Finnish.Gender
