import Linglib.Typology.BodyParts

/-!
# Turkish body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.Turkish

/-- Turkish: distinct *el* (hand) vs *kol* (arm); distinct *parmak* (finger)
    vs *el* (hand). -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Turkish"
  , iso := "tur"
  , family := "Turkic"
  , handArm := some .different
  , fingerHand := some .different }

end Fragments.Turkish
