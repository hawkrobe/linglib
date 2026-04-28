import Linglib.Typology.BodyParts

/-!
# Korean body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.Korean

/-- Korean: distinct hand vs arm; distinct finger vs hand. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Korean"
  , iso := "kor"
  , family := "Koreanic"
  , handArm := some .different
  , fingerHand := some .different }

end Fragments.Korean
