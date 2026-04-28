import Linglib.Typology.Numerals

/-!
# Hindi numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Hindi

/-- Hindi: "first" (*pehla*) suppletive, "second" (*dusra*) partially
    suppletive, higher ordinals regular with *-vam* suffix. Distributive by
    reduplication (*do-do* 'two-two'). No numeral classifiers. *Aur* (and)
    differs from *sab* (all). Obligatory plural; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Hindi"
  , iso := "hin"
  , ordinal := .firstSecondSuppletion
  , distributive := .markedByReduplication
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .southAsia
  , pluralMarking := .obligatory
  , numeralBase := some .decimal }

end Fragments.Hindi
