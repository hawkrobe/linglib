import Linglib.Typology.Pronouns

/-!
# Turkish pronoun profile (WALS Chs 39, 40, 44–48)
@cite{wals-2013}
-/

namespace Fragments.Turkish

/-- Turkish (Turkic). No incl/excl; no gender distinctions (o for all
    genders); binary politeness (sen/siz); generic-noun-based
    indefinites (birisi from bir 'one'); intensifier and reflexive
    identical (kendi); no person marking on adpositions. -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Turkish"
  , family := "Turkic"
  , iso := "tur"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noDistinction
  , genderInPronouns := some .noGenderDistinctions
  , politeness := some .binary
  , indefiniteType := some .genericNounBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

end Fragments.Turkish
