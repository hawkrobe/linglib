import Linglib.Syntax.Adposition.Order

/-!
# Korean adposition order

WALS-derived adposition order for Korean (ISO `kor`). WALS Ch 85
classifies Korean as postpositional.
-/

namespace Korean

/-- Korean adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "kor"

end Korean
