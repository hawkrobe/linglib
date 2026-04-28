import Linglib.Typology.Numerals

/-!
# Thai numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Thai

/-- Thai: ordinals formed with *thi-* prefix (*thi-nung* 'first',
    *thi-song* 'second') — all regular. No morphological distributive.
    Obligatory numeral classifiers (*maa sam tua* 'dog three CL.animal').
    No grammatical plural; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Thai"
  , iso := "tha"
  , ordinal := .allFromCardinals
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .southeastAsia
  , pluralMarking := .none
  , numeralBase := some .decimal }

end Fragments.Thai
