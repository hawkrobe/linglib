import Linglib.Typology.Color

/-!
# Russian color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Fragments.Slavic.Russian

/-- Russian: 6 non-derived basic colors, 11 total basic colors (famously
    distinguishes *sinij* 'dark blue' from *goluboj* 'light blue', but WALS
    counts both within the basic-color count); green (*zelenyj*) vs blue
    (*sinij*) distinct; red vs yellow distinct. -/
def colorProfile : Typology.ColorProfile :=
  { language := "Russian"
  , iso := "rus"
  , family := "Indo-European"
  , nonDerived := some .six
  , basic := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct }

end Fragments.Slavic.Russian
