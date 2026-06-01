import Linglib.Typology.Adposition

/-!
# Tzotzil adposition order

WALS-derived adposition order for Tzotzil (ISO `tzo`). WALS Ch 85
classifies Tzotzil as prepositional.
-/

namespace Tzotzil

/-- Tzotzil adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "tzo"

end Tzotzil
