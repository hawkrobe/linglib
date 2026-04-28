import Linglib.Typology.WordOrder

/-!
# Arabic word-order profile

WALS-derived word-order profile for Modern Standard Arabic (ISO `arb`).
-/

namespace Fragments.Arabic

/-- Arabic word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "arb"

end Fragments.Arabic
