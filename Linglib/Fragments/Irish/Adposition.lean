import Linglib.Syntax.Category.Adposition.Order

/-!
# Irish adposition order

WALS-derived adposition order for Irish (ISO `gle`). WALS Ch 85
classifies Irish as prepositional.
-/

namespace Irish

/-- Irish adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "gle"

end Irish
