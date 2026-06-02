import Linglib.Typology.Numeral.WALS

/-!
# Mandarin numeral profile (WALS Chs 53–56, 131)
[wals-2013]
-/

namespace Mandarin

/-- Mandarin Chinese: ordinals formed regularly with *di-* prefix (*di-yi*
    'first', *di-er* 'second') — no suppletion. No morphological distributive.
    Obligatory numeral classifiers (*san ge ren* 'three CL person'). Conjunction
    *he* and universal *dou* are distinct morphemes. No grammatical plural on
    common nouns; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Mandarin" "cmn" (region := .eastAsia) (pluralMarking := .none)

end Mandarin
