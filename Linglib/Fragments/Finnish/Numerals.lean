import Linglib.Typology.Numeral.WALS

/-!
# Finnish numeral profile (WALS Chs 53–56, 131)
[wals-2013]
-/

namespace Finnish

/-- Finnish: *ensimmäinen* 'first' is suppletive, *toinen* 'second' from *eri*
    'different', higher ordinals regular with *-(n)s* suffix (*kolmas* 'third').
    No morphological distributive. No classifiers. *Ja* (and) differs from
    *kaikki* (all). Obligatory plural with *-t*; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Finnish" "fin" (region := .europe) (pluralMarking := .obligatory)

end Finnish
