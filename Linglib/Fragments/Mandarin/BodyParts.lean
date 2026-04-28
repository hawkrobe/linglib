import Linglib.Typology.BodyParts

/-!
# Mandarin body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.Mandarin

/-- Mandarin Chinese: distinct *shou* (hand) vs *bei*/*gebo* (arm); distinct
    finger vs hand. -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , family := "Sino-Tibetan"
  , handArm := some .different
  , fingerHand := some .different }

end Fragments.Mandarin
