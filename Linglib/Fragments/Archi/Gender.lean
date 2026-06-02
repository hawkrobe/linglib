import Linglib.Typology.Gender

/-!
# Archi Gender
@cite{corbett-2013} @cite{corbett-1991}

WALS @cite{corbett-2013} (Chs 30/31/32) classifies Archi (Nakh-Daghestanian,
ISO `aqc`) as a 4-gender, sex-based, semantic-assignment system. Its four
genders are I (male rationals), II (female rationals), III (most animals and
some inanimates), and IV (the residue); gender shows in pervasive agreement
on verbs and predicates.

@cite{corbett-1991} documents phonological and morphological correlates for
the III/IV split, so the monograph treats assignment as semantic *and formal*
rather than semantic-only — a per-Study override at `Studies/Corbett1991.lean`.
-/

namespace Archi.Gender

open Typology.Gender

/-- Archi gender typology per WALS @cite{corbett-2013}: 4-gender, sex-based,
    semantic assignment (Nakh-Daghestanian). Agreement targets per
    @cite{corbett-1991} (pervasive predicate and verbal agreement). -/
def genderTypology : GenderProfile :=
  .fromWALS "Archi" "aqc"
    (rawGenderCount := 4)
    (genderCountFb := .four)
    (basisFb := .sexBased)
    (assignmentFb := .semanticOnly)
    (agreementTargets := [.predicate, .verb])
    (semanticBases := [.rationality, .sex, .animacy])

example : genderTypology.iso639 = "aqc" ∧ genderTypology.name = "Archi" :=
  ⟨rfl, rfl⟩

end Archi.Gender
