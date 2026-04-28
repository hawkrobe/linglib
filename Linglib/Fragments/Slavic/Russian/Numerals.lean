import Linglib.Typology.Numerals

/-!
# Russian numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Slavic.Russian

/-- Russian: "first" (*pervyj*) suppletive, "second" (*vtoroj*) also
    suppletive, higher ordinals regular (*tretij* 'third', *chetvertyj*
    'fourth'). No morphological distributive (uses prepositional phrase
    *po + dative*). No numeral classifiers. *I* (and) differs from *vse*
    (all). Obligatory plural; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Russian"
  , iso := "rus"
  , ordinal := .firstSecondSuppletion
  , distributive := .noDistributive
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .europe
  , pluralMarking := .obligatory
  , numeralBase := some .decimal }

end Fragments.Slavic.Russian
