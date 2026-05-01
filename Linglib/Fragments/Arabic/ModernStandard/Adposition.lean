import Linglib.Typology.Adposition

/-!
# Arabic adposition order

WALS-derived adposition order for Modern Standard Arabic (ISO `arb`).
WALS Ch 85 classifies Arabic as prepositional.
-/

namespace Fragments.Arabic.ModernStandard

/-- Arabic adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "arb"

end Fragments.Arabic.ModernStandard
