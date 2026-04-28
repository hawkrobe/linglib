import Linglib.Typology.Numerals

/-!
# English numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.English

/-- English: "first" and "second" suppletive, higher ordinals regular (-th
    suffix). No morphological distributive numerals (*two-each*), no numeral
    classifiers, conjunction *and* differs from universal *all*. Obligatory
    plural on nouns; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "English"
  , iso := "eng"
  , ordinal := .firstSecondSuppletion
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .europe
  , pluralMarking := .obligatory
  , numeralBase := some .decimal }

end Fragments.English
