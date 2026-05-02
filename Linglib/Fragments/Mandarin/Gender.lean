import Linglib.Typology.Gender

/-!
# Mandarin Chinese Gender
@cite{corbett-1991} @cite{corbett-2013}

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Fragments.Mandarin.Gender

open Typology.Gender

/-- Mandarin Chinese gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Mandarin Chinese" "cmn"
    (rawGenderCount := 0)

example : genderTypology.iso639 = "cmn" ∧ genderTypology.name = "Mandarin Chinese" :=
  ⟨rfl, rfl⟩

end Fragments.Mandarin.Gender
