import Linglib.Typology.Numerals

/-!
# Korean numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Korean

/-- Korean: ordinals use native numerals + *-jjae* suffix (*cheot-jjae* 'first'
    partially suppletive). Distributive by suffix *-ssik* (*du-ssik* 'two
    each'). Optional numeral classifiers (*se myeong-ui haksaeng* 'three CL
    student'). *Gwa*/*wa* (and) differs from *modu* (all). Optional plural
    with *-deul*; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Korean"
  , iso := "kor"
  , ordinal := .firstSuppletion
  , distributive := .markedBySuffix
  , classifier := .optional
  , conjQuant := .differentiation
  , region := .eastAsia
  , pluralMarking := .optional
  , numeralBase := some .decimal }

end Fragments.Korean
