import Linglib.Typology.Numerals

/-!
# Tseltal numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Mayan.Tseltal

/-- Tseltal (Mayan, Mesoamerica): ordinals not productively formed. Numeral
    classifiers obligatory (distinct from Mayan noun classifiers). No
    morphological distributive. Conjunction and universal quantifier are
    differentiated. No obligatory plural on nouns; vigesimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Tseltal"
  , iso := "tzh"
  , ordinal := .noOrdinals
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .mesoamerica
  , pluralMarking := .none
  , numeralBase := some .vigesimal }

end Fragments.Mayan.Tseltal
