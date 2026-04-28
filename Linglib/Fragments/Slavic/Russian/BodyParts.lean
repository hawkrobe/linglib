import Linglib.Typology.BodyParts

/-!
# Russian body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.Slavic.Russian

/-- Russian: *ruka* covers both 'hand' and 'arm' (identical); distinct
    finger (*palec*) vs hand (*ruka*). -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Russian"
  , iso := "rus"
  , family := "Indo-European"
  , handArm := some .identical
  , fingerHand := some .different }

end Fragments.Slavic.Russian
