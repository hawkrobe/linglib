import Linglib.Typology.Numerals

/-!
# Bengali numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Bengali

/-- Bengali: ordinals formed with *-tho* suffix, but "first" (*prothom*) is
    suppletive. Distributive by reduplication. Optional classifiers (*tin-ta
    boi* 'three-CL book', but bare *tin boi* also grammatical). *Ebong* (and)
    differs from *sob* (all). Optional plural; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Bengali"
  , iso := "ben"
  , ordinal := .firstSuppletion
  , distributive := .markedByReduplication
  , classifier := .optional
  , conjQuant := .differentiation
  , region := .southAsia
  , pluralMarking := .optional
  , numeralBase := some .decimal }

end Fragments.Bengali
