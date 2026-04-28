import Linglib.Typology.BodyParts

/-!
# English body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.English

/-- English: distinct *hand* vs *arm* and *finger* vs *hand*. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "English"
  , iso := "eng"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different }

end Fragments.English
