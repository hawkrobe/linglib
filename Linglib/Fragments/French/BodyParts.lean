import Linglib.Typology.BodyParts

/-!
# French body-part profile (WALS Chs 129–130)
@cite{wals-2013}
-/

namespace Fragments.French

/-- French: distinct *main*/*bras* (hand/arm) and *doigt*/*main* (finger/hand). -/
def bodyPartProfile : Typology.BodyPartProfile :=
  { language := "French"
  , iso := "fra"
  , family := "Indo-European"
  , handArm := some .different
  , fingerHand := some .different }

end Fragments.French
