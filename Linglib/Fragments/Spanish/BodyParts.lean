import Linglib.Typology.BodyParts

/-!
# Spanish body-part profile (WALS Chs 129–130)
[wals-2013]
-/

namespace Spanish

/-- Spanish: distinct *mano*/*brazo* and *dedo*/*mano*. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Spanish"
  , iso := "spa"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different }

end Spanish
