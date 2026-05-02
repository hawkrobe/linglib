import Linglib.Typology.Gender

/-!
# Japanese Gender
@cite{corbett-1991} @cite{corbett-2013}

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Fragments.Japanese.Gender

open Typology.Gender

/-- Japanese gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Japanese" "jpn"
    (rawGenderCount := 0)

example : genderTypology.iso639 = "jpn" ∧ genderTypology.name = "Japanese" :=
  ⟨rfl, rfl⟩

end Fragments.Japanese.Gender
