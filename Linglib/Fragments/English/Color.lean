import Linglib.Typology.Color

/-!
# English color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Fragments.English

/-- English: 6 non-derived basic color categories, 11 total basic colors
    (Berlin-Kay maximum); green vs blue distinct; red vs yellow distinct. -/
def colorProfile : Typology.ColorProfile :=
  { language := "English"
  , iso := "eng"
  , family := "Indo-European"
  , nonDerived := some .six
  , basic := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct }

end Fragments.English
