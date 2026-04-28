import Linglib.Typology.Numerals

/-!
# Mandarin numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Mandarin

/-- Mandarin Chinese: ordinals formed regularly with *di-* prefix (*di-yi*
    'first', *di-er* 'second') — no suppletion. No morphological distributive.
    Obligatory numeral classifiers (*san ge ren* 'three CL person'). Conjunction
    *he* and universal *dou* are distinct morphemes. No grammatical plural on
    common nouns; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Mandarin"
  , iso := "cmn"
  , ordinal := .allFromCardinals
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .eastAsia
  , pluralMarking := .none
  , numeralBase := some .decimal }

end Fragments.Mandarin
