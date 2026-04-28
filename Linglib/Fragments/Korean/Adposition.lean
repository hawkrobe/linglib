import Linglib.Typology.Adposition

/-!
# Korean adposition order

WALS-derived adposition order for Korean (ISO `kor`). WALS Ch 85
classifies Korean as postpositional.
-/

namespace Fragments.Korean

/-- Korean adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "kor"

end Fragments.Korean
