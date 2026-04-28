import Linglib.Typology.Adposition

/-!
# Welsh adposition order

WALS-derived adposition order for Welsh (ISO `cym`). WALS Ch 85
classifies Welsh as prepositional.
-/

namespace Fragments.Welsh

/-- Welsh adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "cym"

end Fragments.Welsh
