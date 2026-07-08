import Linglib.Syntax.Category.Adposition.Order

/-!
# Basque adposition order

WALS-derived adposition order for Basque (ISO `eus`). WALS Ch 85
classifies Basque as postpositional.
-/

namespace Basque

/-- Basque adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "eus"

end Basque
