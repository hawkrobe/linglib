import Linglib.Typology.Gender

/-!
# Romanian Gender
@cite{corbett-1991} @cite{corbett-2013}

3 genders (masc/fem/neuter — the neuter behaves as masc in the singular and
fem in the plural; "ambigeneric"). Sex-based, semantic + formal.
-/

namespace Romanian.Gender

open Typology.Gender

/-- Romanian gender typology: 3-gender sex-based with ambigeneric neuter. -/
def genderTypology : GenderProfile :=
  .fromWALS "Romanian" "ron"
    (rawGenderCount := 3)
    (genderCountFb := .three)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .personalPronoun])
    (semanticBases := [.sex])
    (attestedSurfaceGenders := [.masculine, .feminine, .neuter])

example : genderTypology.iso639 = "ron" ∧ genderTypology.name = "Romanian" :=
  ⟨rfl, rfl⟩

/-- Romanian is in @cite{corbett-1991}'s "canonical" cell. -/
example : genderTypology.IsCanonicalGender := by decide

end Romanian.Gender
