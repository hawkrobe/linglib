import Linglib.Typology.Color

/-!
# Mandarin color profile (WALS Chs 132–135)
[wals-2013]
-/

namespace Mandarin

/-- Mandarin Chinese: 6 non-derived basic colors, 8–8.5 total basic colors;
    green (*lü*) vs blue (*lan*) distinct; red (*hong*) vs yellow (*huang*)
    distinct.
    Derived from the WALS Chs 132–135 rows for `cmn`. -/
def colorProfile : Typology.ColorProfile :=
  Typology.ColorProfile.fromWALS "Mandarin Chinese" "cmn" "Sino-Tibetan"

end Mandarin
