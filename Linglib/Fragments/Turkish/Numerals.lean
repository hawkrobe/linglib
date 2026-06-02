import Linglib.Typology.Numeral.WALS

/-!
# Turkish numeral profile (WALS Chs 53–56, 131)
[wals-2013]
-/

namespace Turkish

/-- Turkish: *birinci* 'first' derived regularly from *bir* 'one' via *-(i)nci*
    suffix (all ordinals so formed). Distributive numerals by suffix *-er*/*-ar*
    (*iki-şer* 'two each'). No obligatory classifiers, but optional classifiers
    exist (*iki tane kitap* 'two CL book'). *Ve* (and) differs from *hepsi*
    (all). Obligatory plural with *-ler*/*-lar*; decimal base. -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Turkish" "tur" (region := .westAsia) (pluralMarking := .obligatory)

end Turkish
