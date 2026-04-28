import Linglib.Typology.Numerals

/-!
# Indonesian numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Indonesian

/-- Indonesian: ordinals with *ke-* prefix (*ke-satu* 'first' regular;
    *pertama* 'first' from Sanskrit also used) — various pattern. No
    morphological distributive. Obligatory numeral classifiers (*tiga orang
    murid* 'three CL student'). *Dan* (and) differs from *semua* (all).
    Optional plural by reduplication; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , ordinal := .various
  , distributive := .noDistributive
  , classifier := .obligatory
  , conjQuant := .differentiation
  , region := .southeastAsia
  , pluralMarking := .optional
  , numeralBase := some .decimal }

end Fragments.Indonesian
