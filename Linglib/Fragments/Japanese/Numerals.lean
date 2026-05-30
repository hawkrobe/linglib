import Linglib.Typology.Numeral.WALS

/-!
# Japanese numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Japanese

/-- Japanese: ordinals formed with *-banme* suffix (*ichi-banme* 'first',
    *ni-banme* 'second') — no suppletion. Distributive by reduplication
    (*hitori-hitori* 'one by one'). Obligatory numeral classifiers (*san-nin*
    'three-CL.person'). Conjunction *to* differs from universal *subete*. No
    grammatical plural on common nouns; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Japanese" "jpn" (region := .eastAsia) (pluralMarking := .none)

end Fragments.Japanese
