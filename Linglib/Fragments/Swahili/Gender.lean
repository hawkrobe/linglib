import Linglib.Typology.Gender

/-!
# Swahili Gender
@cite{corbett-1991} @cite{corbett-2013}

~15 noun classes (singular/plural pairings + locatives). Bantu noun-class
system: semantic + formal assignment via prefixes. Full agreement across
determiners, adjectives, verbs, pronouns, numerals, possessives.

`attestedSurfaceGenders := []` because the 15-class system doesn't fit
the Indo-European `SurfaceGender` enum; per-Fragment lexical files would
expose a fine-grained `Class` type for noun-class agreement morphology.
-/

namespace Fragments.Swahili.Gender

open Typology.Gender
open Core (AgreementTarget)

/-- Swahili gender typology: 15-class Bantu, semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Swahili" "swh"
    (rawGenderCount := 15)
    (genderCountFb := .fivePlus)
    (basisFb := .nonSexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .relativePronoun,
                          .personalPronoun, .verb])
    (semanticBases := [.humanness, .animacy, .shape])

example : genderTypology.iso639 = "swh" ∧ genderTypology.name = "Swahili" :=
  ⟨rfl, rfl⟩

end Fragments.Swahili.Gender
