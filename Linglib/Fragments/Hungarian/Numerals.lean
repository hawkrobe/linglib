import Linglib.Typology.Numerals

/-!
# Hungarian numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Hungarian

/-- Hungarian: "first" (*első*) suppletive, higher ordinals regular with *-dik*
    suffix (*második* 'second', *harmadik* 'third'). Distributive by
    reduplication (*ket-ket* 'two-two'). No numeral classifiers. *És* (and)
    differs from *minden* (all/every). Obligatory plural with *-k*;
    decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , ordinal := .firstSuppletion
  , distributive := .markedByReduplication
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .europe
  , pluralMarking := .obligatory
  , numeralBase := some .decimal }

end Fragments.Hungarian
