import Linglib.Syntax.Category.Adposition.Order

/-!
# Tzotzil adposition order

WALS-derived adposition order for Tzotzil (ISO `tzo`). WALS Ch 85
classifies Tzotzil as prepositional.
-/

namespace Tzotzil

/-- Tzotzil adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "tzo"

end Tzotzil
