import Linglib.Typology.Color

/-!
# Russian color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Russian

/-- Russian: 6 non-derived basic colors, 11 total basic colors (famously
    distinguishes *sinij* 'dark blue' from *goluboj* 'light blue', but WALS
    counts both within the basic-color count); green (*zelenyj*) vs blue
    (*sinij*) distinct; red vs yellow distinct.
    Derived from the WALS Chs 132–135 rows for `rus`. -/
def colorProfile : Typology.ColorProfile :=
  Typology.ColorProfile.fromWALS "Russian" "rus" "Indo-European"

end Russian
