import Linglib.Typology.Color

/-!
# German color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Fragments.German

/-- German: 6 non-derived basic colors, 11 total basic colors; green (*grün*)
    vs blue (*blau*) distinct; red vs yellow distinct. -/
def colorProfile : Typology.ColorProfile :=
  { language := "German"
  , iso := "deu"
  , family := "Indo-European"
  , nonDerived := some .six
  , basic := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct }

end Fragments.German
