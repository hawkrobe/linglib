import Linglib.Typology.Color

/-!
# German color profile (WALS Chs 132–135)
[wals-2013]
-/

namespace German

/-- German: 6 non-derived basic colors, 11 total basic colors; green (*grün*)
    vs blue (*blau*) distinct; red vs yellow distinct.
    Derived from the WALS Chs 132–135 rows for `deu`. -/
def colorProfile : Typology.ColorProfile :=
  Typology.ColorProfile.fromWALS "German" "deu" "Indo-European"

end German
