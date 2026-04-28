import Linglib.Typology.BodyParts

/-!
# Hungarian body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.Hungarian

/-- Hungarian: distinct *kéz* (hand) vs *kar* (arm); distinct *ujj* (finger)
    vs *kéz* (hand). -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , family := "Uralic"
  , handArm := some .different
  , fingerHand := some .different }

end Fragments.Hungarian
