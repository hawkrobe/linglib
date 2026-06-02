import Linglib.Typology.Numeral.WALS

/-!
# Vietnamese numeral profile (WALS Chs 53–56, 131)
[wals-2013]
-/

namespace Vietnamese

/-- Vietnamese: ordinals formed with *thu* prefix (*thu nhat* 'first',
    *thu hai* 'second') — regular. No morphological distributive. Obligatory
    classifiers (*ba con meo* 'three CL cat'). No grammatical plural;
    decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Vietnamese" "vie" (region := .southeastAsia) (pluralMarking := .none)

end Vietnamese
