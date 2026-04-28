import Linglib.Typology.Pronouns

/-!
# Hindi/Urdu pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.HindiUrdu

/-- Hindi (Indo-European, Indo-Aryan). No incl/excl; no person
    marking on verbs (WALS); no gender distinctions in pronouns
    (vah/ye are gender-neutral); multiple politeness distinctions
    (tu/tum/aap); special indefinite forms (koi, kuch); intensifier
    and reflexive identical (apne-aap/khud); no person marking on
    adpositions. -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Hindi"
  , family := "Indo-European"
  , iso := "hin"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .multiple
  , indefiniteType := some .special
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

end Fragments.HindiUrdu
