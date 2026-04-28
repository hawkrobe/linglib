import Linglib.Typology.Pronouns

/-!
# French pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.French

/-- French (Indo-European, Romance). No incl/excl; gender in 3rd sg
    (il/elle); binary politeness (tu/vous); generic-noun-based
    indefinites (quelqu'un); intensifier (même) differentiated from
    reflexive (se); no person marking on adpositions. -/
def pronounProfile : Typology.PronounProfile :=
  { language := "French"
  , family := "Indo-European"
  , iso := "fra"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .in3rdPersonSgOnly
  , politeness := some .binary
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .differentiated
  , personMarkingAdpositions := some .noPersonMarking }

end Fragments.French
