import Linglib.Typology.Numerals

/-!
# Vietnamese numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Vietnamese

/-- Vietnamese: ordinals formed with *thu* prefix (*thu nhat* 'first',
    *thu hai* 'second') — regular. No morphological distributive. Obligatory
    classifiers (*ba con meo* 'three CL cat'). No grammatical plural;
    decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Vietnamese"
  , iso := "vie"
  , ordinal := .allFromCardinals
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .southeastAsia
  , pluralMarking := .none
  , numeralBase := some .decimal }

end Fragments.Vietnamese
