import Linglib.Syntax.Category.Adposition.Order

/-!
# Mandarin adposition order

WALS-derived adposition order for Mandarin (ISO `cmn`). WALS Ch 85
classifies Mandarin as having both prepositions and postpositions
(no dominant order).
-/

namespace Mandarin

/-- Mandarin adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "cmn"

end Mandarin
