import Linglib.Typology.BodyParts

/-!
# Swahili body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.Swahili

/-- Swahili: *mkono* covers both 'hand' and 'arm' (identical); distinct
    finger vs hand. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Swahili"
  , iso := "swh"
  , family := "Niger-Congo"
  , handArm := some .identical
  , fingerHand := some .different }

end Fragments.Swahili
