import Linglib.Typology.Numeral.WALS

/-!
# Hungarian numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Hungarian

/-- Hungarian: "first" (*első*) suppletive, higher ordinals regular with *-dik*
    suffix (*második* 'second', *harmadik* 'third'). Distributive by
    reduplication (*ket-ket* 'two-two'). No numeral classifiers. *És* (and)
    differs from *minden* (all/every). Obligatory plural with *-k*;
    decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Hungarian" "hun" (region := .europe) (pluralMarking := .obligatory)

end Hungarian
