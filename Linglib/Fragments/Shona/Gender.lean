import Linglib.Typology.Gender

/-!
# Shona Gender
@cite{corbett-1991} @cite{corbett-2013}

Bantu noun-class system. Carstens 2026 cites 8 active gender classes.
-/

namespace Fragments.Shona.Gender

open Typology.Gender

/-- Shona gender typology: noun-class Bantu, semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Shona" "sna"
    (rawGenderCount := 8)
    (genderCountFb := .fivePlus)
    (basisFb := .nonSexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .relativePronoun,
                          .personalPronoun, .verb])
    (semanticBases := [.humanness])

example : genderTypology.iso639 = "sna" ∧ genderTypology.name = "Shona" :=
  ⟨rfl, rfl⟩

/-- Shona is a noun-class system (Bantu, 8 classes per @cite{carstens-2026}). -/
example : genderTypology.IsNounClassSystem := by decide

end Fragments.Shona.Gender
