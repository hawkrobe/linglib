import Linglib.Typology.Adposition

/-!
# Swahili adposition order

WALS-derived adposition order for Swahili (ISO `swh`). WALS Ch 85
classifies Swahili as prepositional.
-/

namespace Fragments.Swahili

/-- Swahili adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "swh"

end Fragments.Swahili
