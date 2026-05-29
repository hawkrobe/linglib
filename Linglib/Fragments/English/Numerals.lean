import Linglib.Typology.Numeral.WALS

/-!
# English numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.English

/-- English: "first" and "second" suppletive, higher ordinals regular (-th
    suffix). No morphological distributive numerals (*two-each*), no numeral
    classifiers, conjunction *and* differs from universal *all*. Obligatory
    plural on nouns; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "English" "eng" (region := .europe) (pluralMarking := .obligatory)

end Fragments.English
