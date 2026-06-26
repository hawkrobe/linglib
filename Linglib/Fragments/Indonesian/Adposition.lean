import Linglib.Syntax.Adposition.Order

/-!
# Indonesian adposition order

WALS-derived adposition order for Indonesian (ISO `ind`). WALS Ch 85
classifies Indonesian as prepositional.
-/

namespace Indonesian

/-- Indonesian adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "ind"

end Indonesian
