import Linglib.Typology.Numeral.WALS

/-!
# Burmese numeral profile (WALS Chs 53–56, 131)
[wals-2013]
-/

namespace Burmese

/-- Burmese: ordinals formed with prefix (*pa-hta-ma* 'first' from inherited
    Pali; modern ordinals use *tha-* prefix); various pattern. Numeral
    classifiers obligatory (*lu thon yauk* 'person three CL'). No
    morphological distributive. No grammatical plural; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Burmese" "mya" (region := .southeastAsia) (pluralMarking := .none)

end Burmese
