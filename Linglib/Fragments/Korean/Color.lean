import Linglib.Typology.Color

/-!
# Korean color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Korean

/-- Korean: 6 non-derived basic colors, 11 total basic colors; green vs blue
    distinct; red vs yellow distinct.
    Derived from the WALS Chs 132–135 rows for `kor`. -/
def colorProfile : Typology.ColorProfile :=
  Typology.ColorProfile.fromWALS "Korean" "kor" "Koreanic"

end Korean
