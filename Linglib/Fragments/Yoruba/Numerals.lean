import Linglib.Typology.Numerals

/-!
# Yoruba numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Yoruba

/-- Yoruba: ordinals formed with *(i)keji* prefix system, varying patterns
    across the paradigm. No morphological distributive. No numeral classifiers.
    Conjunction *ati* and universal quantifier *gbogbo* are distinct. Plural
    marked optionally (*awon*); vigesimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Yoruba"
  , iso := "yor"
  , ordinal := .various
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .africa
  , pluralMarking := .optional
  , numeralBase := some .vigesimal }

end Fragments.Yoruba
