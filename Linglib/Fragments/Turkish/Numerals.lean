import Linglib.Typology.Numerals

/-!
# Turkish numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Fragments.Turkish

/-- Turkish: *birinci* 'first' derived regularly from *bir* 'one' via *-(i)nci*
    suffix (all ordinals so formed). Distributive numerals by suffix *-er*/*-ar*
    (*iki-şer* 'two each'). No obligatory classifiers, but optional classifiers
    exist (*iki tane kitap* 'two CL book'). *Ve* (and) differs from *hepsi*
    (all). Obligatory plural with *-ler*/*-lar*; decimal base. -/
def numeralProfile : Typology.NumeralProfile :=
  { language := "Turkish"
  , iso := "tur"
  , ordinal := .allFromCardinals
  , distributive := .markedBySuffix
  , classifier := .optional
  , conjQuant := .differentiation
  , region := .westAsia
  , pluralMarking := .obligatory
  , numeralBase := some .decimal }

end Fragments.Turkish
