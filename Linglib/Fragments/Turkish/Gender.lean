import Linglib.Features.Gender.Profile

/-!
# Turkish Gender
[corbett-1991] [corbett-2013]

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Turkish.Gender

open _root_.Gender

/-- Turkish gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Turkish" "tur"
    (rawGenderCount := 0)

theorem genderTypology_iso639 : genderTypology.iso639 = "tur" := rfl

theorem genderTypology_name : genderTypology.name = "Turkish" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

end Turkish.Gender
