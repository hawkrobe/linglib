import Linglib.Syntax.Category.Adposition.Order

/-!
# Arabic adposition order

WALS-derived adposition order for Modern Standard Arabic (ISO `arb`).
WALS Ch 85 classifies Arabic as prepositional.
-/

namespace Arabic.ModernStandard

/-- Arabic adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "arb"

end Arabic.ModernStandard
