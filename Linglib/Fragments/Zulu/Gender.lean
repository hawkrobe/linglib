import Linglib.Typology.Gender

/-!
# Zulu Gender
@cite{corbett-1991} @cite{corbett-2013}

~15 noun classes. Bantu noun-class system parallel to Swahili.
-/

namespace Fragments.Zulu.Gender

open Typology.Gender
open Core (AgreementTarget)

/-- Zulu gender typology: 15-class Bantu, semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Zulu" "zul"
    (rawGenderCount := 15)
    (genderCountFb := .fivePlus)
    (basisFb := .nonSexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .relativePronoun,
                          .personalPronoun, .verb])
    (semanticBases := [.humanness, .animacy, .shape])

example : genderTypology.iso639 = "zul" ∧ genderTypology.name = "Zulu" :=
  ⟨rfl, rfl⟩

end Fragments.Zulu.Gender
