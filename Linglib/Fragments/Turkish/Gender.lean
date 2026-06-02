import Linglib.Typology.Gender

/-!
# Turkish Gender
[corbett-1991] [corbett-2013]

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Turkish.Gender

open Typology.Gender

/-- Turkish gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Turkish" "tur"
    (rawGenderCount := 0)

example : genderTypology.iso639 = "tur" ∧ genderTypology.name = "Turkish" :=
  ⟨rfl, rfl⟩

end Turkish.Gender
