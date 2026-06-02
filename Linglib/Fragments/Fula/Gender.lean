import Linglib.Typology.Gender

/-!
# Fula Gender
[corbett-1991] [corbett-2013]

~20+ noun classes (Atlantic, Niger-Congo). One of the richest class systems
in Africa. Sample maximum in Corbett's 22-language exemplar.
-/

namespace Fula.Gender

open Typology.Gender

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

/-- Fula is a noun-class system (20+ classes per [corbett-1991]). -/
example : genderTypology.IsNounClassSystem := by decide

end Fula.Gender
