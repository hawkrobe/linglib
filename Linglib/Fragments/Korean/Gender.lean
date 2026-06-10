import Linglib.Morphology.Gender

/-!
# Korean Gender
[corbett-1991] [corbett-2013]

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Korean.Gender

open Morphology.Gender

/-- Korean gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Korean" "kor"
    (rawGenderCount := 0)

theorem genderTypology_iso639 : genderTypology.iso639 = "kor" := rfl

theorem genderTypology_name : genderTypology.name = "Korean" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

end Korean.Gender
