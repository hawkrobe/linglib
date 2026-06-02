import Linglib.Typology.BodyParts

/-!
# Tagalog body-part profile (WALS Chs 129–130)
[wals-2013]
-/

namespace Tagalog

/-- Tagalog: distinct hand vs arm; distinct finger vs hand. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , family := "Austronesian"
  , handArm := some .different
  , fingerHand := some .different }

end Tagalog
