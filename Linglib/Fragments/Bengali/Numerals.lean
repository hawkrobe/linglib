import Linglib.Typology.Numeral.WALS

/-!
# Bengali numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Bengali

/-- Bengali: ordinals formed with *-tho* suffix, but "first" (*prothom*) is
    suppletive. Distributive by reduplication. Optional classifiers (*tin-ta
    boi* 'three-CL book', but bare *tin boi* also grammatical). *Ebong* (and)
    differs from *sob* (all). Optional plural; decimal base. -/
def numeralProfile : Numeral.Profile :=
  -- Bengali (iso `ben`) is absent from WALS Ch 131; decimal base is curated.
  { Numeral.Profile.fromWALS "Bengali" "ben" (region := .southAsia)
      (pluralMarking := .optional) with
    numeralBase := some .decimal }

end Bengali
