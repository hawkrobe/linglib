import Linglib.Typology.Numeral.WALS

/-!
# Thai numeral profile (WALS Chs 53–56, 131)
[wals-2013]
-/

namespace Thai

/-- Thai: ordinals formed with *thi-* prefix (*thi-nung* 'first',
    *thi-song* 'second') — all regular. No morphological distributive.
    Obligatory numeral classifiers (*maa sam tua* 'dog three CL.animal').
    No grammatical plural; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Thai" "tha" (region := .southeastAsia) (pluralMarking := .none)

end Thai
