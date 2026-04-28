import Linglib.Typology.Numerals

/-!
# Swahili numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Swahili

/-- Swahili: ordinals formed with *-a* prefix + cardinal (*wa-kwanza* 'first'
    has distinct root, *-a-pili* 'second' onward regular). No morphological
    distributive. No numeral classifiers (noun class system serves a different
    function). *Na* (and) differs from *-ote* (all). Obligatory plural via
    noun class prefixes; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Swahili"
  , iso := "swh"
  , ordinal := .firstSuppletion
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .africa
  , pluralMarking := .obligatory
  , numeralBase := some .decimal }

end Fragments.Swahili
