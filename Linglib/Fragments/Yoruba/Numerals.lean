import Linglib.Typology.Numeral.WALS

/-!
# Yoruba numeral profile (WALS Chs 53–56, 131)
[wals-2013]
-/

namespace Yoruba

/-- Yoruba: ordinals formed with *(i)keji* prefix system, varying patterns
    across the paradigm. No morphological distributive. No numeral classifiers.
    Conjunction *ati* and universal quantifier *gbogbo* are distinct. Plural
    marked optionally (*awon*); vigesimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Yoruba" "yor" (region := .africa) (pluralMarking := .optional)

end Yoruba
