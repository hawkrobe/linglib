import Linglib.Typology.Numeral.WALS

/-!
# Indonesian numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Indonesian

/-- Indonesian: ordinals with *ke-* prefix (*ke-satu* 'first' regular;
    *pertama* 'first' from Sanskrit also used) — various pattern. No
    morphological distributive. Obligatory numeral classifiers (*tiga orang
    murid* 'three CL student'). *Dan* (and) differs from *semua* (all).
    Optional plural by reduplication; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Indonesian" "ind" (region := .southeastAsia) (pluralMarking := .optional)

end Indonesian
