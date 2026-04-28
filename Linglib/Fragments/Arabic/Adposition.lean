import Linglib.Typology.Adposition

/-!
# Arabic adposition order

WALS-derived adposition order for Modern Standard Arabic (ISO `arb`).
WALS Ch 85 classifies Arabic as prepositional.
-/

namespace Fragments.Arabic

/-- Arabic adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "arb"

end Fragments.Arabic
