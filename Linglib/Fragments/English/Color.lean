import Linglib.Typology.Color

/-!
# English color profile (WALS Chs 132–135)
[wals-2013]
-/

namespace English

/-- English: 6 non-derived basic color categories, 11 total basic colors
    (Berlin-Kay maximum); green vs blue distinct; red vs yellow distinct.
    Derived from the WALS Chs 132–135 rows for `eng`. -/
def colorProfile : Typology.ColorProfile :=
  Typology.ColorProfile.fromWALS "English" "eng" "Indo-European"

end English
