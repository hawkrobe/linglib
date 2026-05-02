import Linglib.Typology.Gender

/-!
# Korean Gender
@cite{corbett-1991} @cite{corbett-2013}

No grammatical gender. WALS Ch 30/31/32 = none.
-/

namespace Fragments.Korean.Gender

open Typology.Gender
open Core (AgreementTarget)

/-- Korean gender typology: no gender. -/
def genderTypology : GenderProfile :=
  .fromWALS "Korean" "kor"
    (rawGenderCount := 0)

example : genderTypology.iso639 = "kor" ∧ genderTypology.name = "Korean" :=
  ⟨rfl, rfl⟩

end Fragments.Korean.Gender
