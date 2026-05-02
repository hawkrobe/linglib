import Linglib.Typology.Gender

/-!
# Finnish Gender
@cite{corbett-1991} @cite{corbett-2013}

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Fragments.Finnish.Gender

open Typology.Gender

/-- Finnish gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Finnish" "fin"
    (rawGenderCount := 0)

example : genderTypology.iso639 = "fin" ∧ genderTypology.name = "Finnish" :=
  ⟨rfl, rfl⟩

end Fragments.Finnish.Gender
