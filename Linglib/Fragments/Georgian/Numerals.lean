import Linglib.Typology.Numeral.WALS

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
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Georgian" "kat" (region := .westAsia) (pluralMarking := .obligatory)

end Fragments.Georgian
