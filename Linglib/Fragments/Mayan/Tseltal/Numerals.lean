import Linglib.Typology.Numeral.WALS

/-!
# Tseltal numeral profile (WALS Chs 53–56, 131)
[wals-2013]
-/

namespace Tseltal

/-- Tseltal (Mayan, Mesoamerica): ordinals not productively formed. Numeral
    classifiers obligatory (distinct from Mayan noun classifiers). No
    morphological distributive. Conjunction and universal quantifier are
    differentiated. No obligatory plural on nouns; vigesimal base. -/
def numeralProfile : Numeral.Profile :=
  -- Tseltal (iso `tzh`) is in WALS only for Ch 55 (classifiers); ordinal and
  -- base are curated (absent from Chs 53/131).
  { Numeral.Profile.fromWALS "Tseltal" "tzh" (region := .mesoamerica)
      (pluralMarking := .none) with
    ordinal := .noOrdinals
    numeralBase := some .vigesimal }

end Tseltal
