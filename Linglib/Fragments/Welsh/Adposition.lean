import Linglib.Typology.Adposition

/-!
# Welsh adposition order

WALS-derived adposition order for Welsh (ISO `cym`). WALS Ch 85
classifies Welsh as prepositional.
-/

namespace Fragments.Welsh

/-- Welsh adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "cym"

end Fragments.Welsh
