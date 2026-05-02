import Linglib.Typology.Gender

/-!
# Fula Gender
@cite{corbett-1991} @cite{corbett-2013}

~20+ noun classes (Atlantic, Niger-Congo). One of the richest class systems
in Africa. Sample maximum in Corbett's 22-language exemplar.
-/

namespace Fragments.Fula.Gender

open Typology.Gender
open Core (AgreementTarget)

/-- Fula gender typology: 20-class Atlantic, semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Fula" "ful"
    (rawGenderCount := 20)
    (genderCountFb := .fivePlus)
    (basisFb := .nonSexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .personalPronoun, .verb])
    (semanticBases := [.humanness, .animacy, .shape])

example : genderTypology.iso639 = "ful" ∧ genderTypology.name = "Fula" :=
  ⟨rfl, rfl⟩

end Fragments.Fula.Gender
