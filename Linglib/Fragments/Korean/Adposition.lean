import Linglib.Typology.Adposition

/-!
# Korean adposition order

WALS-derived adposition order for Korean (ISO `kor`). WALS Ch 85
classifies Korean as postpositional.
-/

namespace Korean

/-- Korean adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "kor"

end Korean
