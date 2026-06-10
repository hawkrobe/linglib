import Linglib.Morphology.Gender

/-!
# Zulu Gender
[corbett-1991] [corbett-2013] [poulos-msimang-1998]

Bantu noun-class system parallel to Swahili: 8 controller genders — the
singular/plural pairings 1/2, 3/4, 5/6, 7/8, 9/10, 11/10, 14, 15 — over
the 15-class Nguni inventory of [poulos-msimang-1998] §1.2 (classes 1,
2, 1a, 2b, 3–11, 14, 15; 12 and 13 absent). Classes 1a/2b "use the same
concords as classes 1 and 2"; class 11 plurals fall in class 10; class
15 infinitives show no singular/plural distinction; locative classes
16/17/18 are number-neutral. The count applies [corbett-1991]'s pairing
convention (§6.3, as in his Table 3.4 for Swahili) to those concord
facts.
-/

namespace Zulu.Gender

open Morphology.Gender

/-- Zulu gender typology: 8 controller genders (Bantu), semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Zulu" "zul"
    (rawGenderCount := 8)
    (agreementTargets := [.attributive, .predicate, .relativePronoun,
                          .personalPronoun, .verb])
    (semanticBases := [.humanness, .animacy, .shape])

theorem genderTypology_iso639 : genderTypology.iso639 = "zul" := rfl

theorem genderTypology_name : genderTypology.name = "Zulu" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- Zulu is a noun-class system (5+ genders per [corbett-1991]). -/
theorem isNounClassSystem_genderTypology :
    genderTypology.IsNounClassSystem := by decide

end Zulu.Gender
