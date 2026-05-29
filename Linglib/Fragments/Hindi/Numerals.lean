import Linglib.Typology.Numeral.WALS

/-!
# Hindi numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Hindi

/-- Hindi: "first" (*pehla*) suppletive, "second" (*dusra*) partially
    suppletive, higher ordinals regular with *-vam* suffix. Distributive by
    reduplication (*do-do* 'two-two'). No numeral classifiers. *Aur* (and)
    differs from *sab* (all). Obligatory plural; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Hindi" "hin" (region := .southAsia) (pluralMarking := .obligatory)

end Fragments.Hindi
