import Linglib.Typology.Adposition

/-!
# Irish adposition order

WALS-derived adposition order for Irish (ISO `gle`). WALS Ch 85
classifies Irish as prepositional.
-/

namespace Fragments.Irish

/-- Irish adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "gle"

end Fragments.Irish
