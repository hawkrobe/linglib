import Linglib.Typology.Gender

/-!
# Turkish Gender
@cite{corbett-1991} @cite{corbett-2013}

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Fragments.Turkish.Gender

open Typology.Gender
open Core (AgreementTarget)

/-- Turkish gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Turkish" "tur"
    (rawGenderCount := 0)

example : genderTypology.iso639 = "tur" ∧ genderTypology.name = "Turkish" :=
  ⟨rfl, rfl⟩

end Fragments.Turkish.Gender
