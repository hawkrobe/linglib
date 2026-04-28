import Linglib.Typology.Numerals

/-!
# Finnish numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Finnish

/-- Finnish: *ensimmäinen* 'first' is suppletive, *toinen* 'second' from *eri*
    'different', higher ordinals regular with *-(n)s* suffix (*kolmas* 'third').
    No morphological distributive. No classifiers. *Ja* (and) differs from
    *kaikki* (all). Obligatory plural with *-t*; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Finnish"
  , iso := "fin"
  , ordinal := .firstSecondSuppletion
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .europe
  , pluralMarking := .obligatory
  , numeralBase := some .decimal }

end Fragments.Finnish
