import Linglib.Typology.Color

/-!
# Spanish color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Spanish

/-- Spanish: 6 non-derived basic colors, 11 total basic colors; green (*verde*)
    vs blue (*azul*) distinct; red vs yellow distinct.
    Derived from the WALS Chs 132–135 rows for `spa`. -/
def colorProfile : Typology.ColorProfile :=
  Typology.ColorProfile.fromWALS "Spanish" "spa" "Indo-European"

end Spanish
