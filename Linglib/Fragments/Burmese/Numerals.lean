import Linglib.Typology.Numerals

/-!
# Burmese numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Burmese

/-- Burmese: ordinals formed with prefix (*pa-hta-ma* 'first' from inherited
    Pali; modern ordinals use *tha-* prefix); various pattern. Numeral
    classifiers obligatory (*lu thon yauk* 'person three CL'). No
    morphological distributive. No grammatical plural; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Burmese"
  , iso := "mya"
  , ordinal := .various
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .southeastAsia
  , pluralMarking := .none
  , numeralBase := some .decimal }

end Fragments.Burmese
