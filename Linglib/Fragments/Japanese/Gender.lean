import Linglib.Features.Gender.Profile

/-!
# Japanese Gender
[corbett-1991] [corbett-2013]

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Japanese.Gender

open Gender

/-- Japanese gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Japanese" "jpn"
    (rawGenderCount := 0)

theorem genderTypology_iso639 : genderTypology.iso639 = "jpn" := rfl

theorem genderTypology_name : genderTypology.name = "Japanese" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

end Japanese.Gender
