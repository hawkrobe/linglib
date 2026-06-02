import Linglib.Typology.Numeral.WALS

/-!
# Swahili numeral profile (WALS Chs 53–56, 131)
[wals-2013]
-/

namespace Swahili

/-- Swahili: ordinals formed with *-a* prefix + cardinal (*wa-kwanza* 'first'
    has distinct root, *-a-pili* 'second' onward regular). No morphological
    distributive. No numeral classifiers (noun class system serves a different
    function). *Na* (and) differs from *-ote* (all). Obligatory plural via
    noun class prefixes; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Swahili" "swh" (region := .africa) (pluralMarking := .obligatory)

end Swahili
