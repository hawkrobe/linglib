import Linglib.Typology.BodyParts

/-!
# Tagalog body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.Tagalog

/-- Tagalog: distinct hand vs arm; distinct finger vs hand. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , family := "Austronesian"
  , handArm := some .different
  , fingerHand := some .different }

end Fragments.Tagalog
