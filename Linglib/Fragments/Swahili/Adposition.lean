import Linglib.Typology.Adposition

/-!
# Swahili adposition order

WALS-derived adposition order for Swahili (ISO `swh`). WALS Ch 85
classifies Swahili as prepositional.
-/

namespace Fragments.Swahili

/-- Swahili adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "swh"

end Fragments.Swahili
