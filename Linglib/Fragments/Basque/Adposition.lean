import Linglib.Typology.Adposition

/-!
# Basque adposition order

WALS-derived adposition order for Basque (ISO `eus`). WALS Ch 85
classifies Basque as postpositional.
-/

namespace Fragments.Basque

/-- Basque adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "eus"

end Fragments.Basque
