import Linglib.Syntax.Adposition.Order

/-!
# Swahili adposition order

WALS-derived adposition order for Swahili (ISO `swh`). WALS Ch 85
classifies Swahili as prepositional.
-/

namespace Swahili

/-- Swahili adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "swh"

end Swahili
