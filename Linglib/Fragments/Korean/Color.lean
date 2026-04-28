import Linglib.Typology.Color

/-!
# Korean color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Fragments.Korean

/-- Korean: 6 non-derived basic colors, 11 total basic colors; green vs blue
    distinct; red vs yellow distinct. -/
def colorProfile : Typology.ColorProfile :=
  { language := "Korean"
  , iso := "kor"
  , family := "Koreanic"
  , nonDerived := some .six
  , basic := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct }

end Fragments.Korean
