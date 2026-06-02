import Linglib.Typology.Color

/-!
# French color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace French

/-- French: 6 non-derived basic colors, 11 total basic colors; green (*vert*)
    vs blue (*bleu*) distinct; red vs yellow distinct.
    Derived from the WALS Chs 132–135 rows for `fra`. -/
def colorProfile : Typology.ColorProfile :=
  Typology.ColorProfile.fromWALS "French" "fra" "Indo-European"

end French
