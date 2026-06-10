import Linglib.Morphology.Gender

/-!
# Archi Gender
[corbett-2013] [corbett-1991]

WALS [corbett-2013] (Chs 30/31/32) classifies Archi (Nakh-Daghestanian,
ISO `aqc`) as a 4-gender, sex-based, semantic-assignment system. Its four
genders are I (male rationals), II (female rationals), III (most animals and
some inanimates), and IV (the residue); gender shows in pervasive agreement
on verbs and predicates.

[corbett-1991] documents phonological and morphological correlates for
the III/IV split, so the monograph treats assignment as semantic *and formal*
rather than semantic-only — a per-Study override at `Studies/Corbett1991.lean`.
-/

namespace Archi.Gender

open Morphology.Gender

/-- Archi gender typology per WALS [corbett-2013]: 4-gender, sex-based,
    semantic assignment (Nakh-Daghestanian). Agreement targets per
    [corbett-1991] (pervasive predicate and verbal agreement). -/
def genderTypology : GenderProfile :=
  .fromWALS "Archi" "aqc"
    (rawGenderCount := 4)
    (agreementTargets := [.predicate, .verb])
    (semanticBases := [.rationality, .sex, .animacy])

theorem genderTypology_iso639 : genderTypology.iso639 = "aqc" := rfl

theorem genderTypology_name : genderTypology.name = "Archi" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

end Archi.Gender
