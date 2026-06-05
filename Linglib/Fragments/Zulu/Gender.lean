import Linglib.Typology.Gender

/-!
# Zulu Gender
[corbett-1991] [corbett-2013]

Bantu noun-class system parallel to Swahili: 8 controller genders
(singular/plural pairings 1/2, 3/4, 5/6, 7/8, 9/10, 11/10, 14, 15;
class 1a/2a nouns take 1/2 concords) over ~15 traditional noun classes.
The count applies [corbett-1991]'s pairing convention (§6.3, as in his
Table 3.4 for Swahili) to the standard Nguni inventory; Corbett 1991
mentions Zulu only in passing.
-- UNVERIFIED: the figure 8 is not yet checked against a dedicated Zulu
grammar.
-/

namespace Zulu.Gender

open Typology.Gender

/-- Zulu gender typology: 8 controller genders (Bantu), semantic + formal. -/
def genderTypology : GenderProfile :=
  .fromWALS "Zulu" "zul"
    (rawGenderCount := 8)
    (genderCountFb := .fivePlus)
    (basisFb := .nonSexBased)
    (assignmentFb := .semanticAndFormal)
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
