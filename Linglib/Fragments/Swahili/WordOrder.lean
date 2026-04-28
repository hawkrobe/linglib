import Linglib.Typology.WordOrder

/-!
# Swahili word-order profile

WALS-derived word-order profile for Swahili (ISO `swh`).
-/

namespace Fragments.Swahili

/-- Swahili word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "swh"

end Fragments.Swahili
