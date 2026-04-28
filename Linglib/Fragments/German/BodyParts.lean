import Linglib.Typology.BodyParts

/-!
# German body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.German

/-- German: distinct *Hand*/*Arm* and *Finger*/*Hand*. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "German"
  , iso := "deu"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different }

end Fragments.German
