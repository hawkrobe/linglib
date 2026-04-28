import Linglib.Typology.Numerals

/-!
# Georgian numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Georgian

/-- Georgian: ordinals formed with *me-…-e* circumfix (*me-or-e* 'second',
    *me-sam-e* 'third'); "first" (*p'irveli*) is suppletive. Distributive by
    suffix *-agan* (*or-agan* 'two each'). No numeral classifiers. *Da* (and)
    differs from *q'vela* (all). Obligatory plural; hybrid vigesimal-decimal
    base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Georgian"
  , iso := "kat"
  , ordinal := .firstSuppletion
  , distributive := .markedBySuffix
  , classifier := .absent
  , conjQuant := .differentiation
  , region := .westAsia
  , pluralMarking := .obligatory
  , numeralBase := some .hybridVigesimalDecimal }

end Fragments.Georgian
