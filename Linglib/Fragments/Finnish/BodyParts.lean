import Linglib.Typology.BodyParts

/-!
# Finnish body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.Finnish

/-- Finnish: distinct *käsi* (hand) vs *käsivarsi* (arm); distinct *sormi*
    (finger) vs *käsi* (hand). -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Finnish"
  , iso := "fin"
  , family := "Uralic"
  , handArm := some .different
  , fingerHand := some .different }

end Fragments.Finnish
