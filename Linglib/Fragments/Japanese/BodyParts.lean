import Linglib.Typology.BodyParts

/-!
# Japanese body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.Japanese

/-- Japanese: *te* covers both 'hand' and 'arm' (identical); distinct finger
    (*yubi*) vs hand (*te*). -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , family := "Japonic"
  , handArm := some .identical
  , fingerHand := some .different }

end Fragments.Japanese
