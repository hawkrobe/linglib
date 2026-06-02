import Linglib.Typology.BodyParts

/-!
# German body-part profile (WALS Chs 129–130)
[wals-2013]
-/

namespace German

/-- German: distinct *Hand*/*Arm* and *Finger*/*Hand*. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "German"
  , iso := "deu"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different }

end German
