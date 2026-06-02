import Linglib.Typology.BodyParts

/-!
# English body-part profile (WALS Chs 129–130)
[wals-2013]
-/

namespace English

/-- English: distinct *hand* vs *arm* and *finger* vs *hand*. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "English"
  , iso := "eng"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different }

end English
