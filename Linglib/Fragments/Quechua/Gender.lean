import Linglib.Typology.Gender

/-!
# Quechua Gender
[corbett-1991] [corbett-2013]

No grammatical gender — pan-Quechuan property. Corbett 1991 cites Cusco
Quechua (`quz`) specifically; the Imbabura variety (`qvi`) used by
`Fragments/Quechua/Morph.lean` shows the same no-gender profile.
-/

namespace Quechua.Gender

open Typology.Gender

/-- Cusco Quechua gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Quechua (Cusco)" "quz"
    (rawGenderCount := 0)

example : genderTypology.iso639 = "quz" ∧ genderTypology.name = "Quechua (Cusco)" :=
  ⟨rfl, rfl⟩

end Quechua.Gender
