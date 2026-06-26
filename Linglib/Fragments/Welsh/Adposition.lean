import Linglib.Syntax.Adposition.Order

/-!
# Welsh adposition order

WALS-derived adposition order for Welsh (ISO `cym`). WALS Ch 85
classifies Welsh as prepositional.
-/

namespace Welsh

/-- Welsh adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "cym"

end Welsh
