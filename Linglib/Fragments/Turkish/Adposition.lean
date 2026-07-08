import Linglib.Syntax.Category.Adposition.Order

/-!
# Turkish adposition order

WALS-derived adposition order for Turkish (ISO `tur`). WALS Ch 85
classifies Turkish as postpositional.
-/

namespace Turkish

/-- Turkish adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "tur"

end Turkish
