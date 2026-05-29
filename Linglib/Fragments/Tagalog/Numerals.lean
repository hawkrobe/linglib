import Linglib.Typology.Numeral.WALS

/-!
# Tagalog numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Tagalog

/-- Tagalog: ordinals with *pang-* prefix (*pang-una* 'first' from *una*
    'precede', *pang-alawa* 'second'). Distributive by reduplication
    (*dalawa-dalawa* 'two-two'). No obligatory numeral classifiers (linkers
    *na*/*ng* serve a different function). *At* (and) and *lahat* (all) are
    differentiated. Optional plural (*mga*); decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Tagalog" "tgl" (region := .southeastAsia) (pluralMarking := .optional)

end Fragments.Tagalog
