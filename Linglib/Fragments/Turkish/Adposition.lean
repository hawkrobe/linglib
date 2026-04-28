import Linglib.Typology.Adposition

/-!
# Turkish adposition order

WALS-derived adposition order for Turkish (ISO `tur`). WALS Ch 85
classifies Turkish as postpositional.
-/

namespace Fragments.Turkish

/-- Turkish adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "tur"

end Fragments.Turkish
