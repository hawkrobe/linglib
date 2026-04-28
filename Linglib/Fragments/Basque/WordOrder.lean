import Linglib.Typology.WordOrder

/-!
# Basque word-order profile

WALS-derived word-order profile for Basque (ISO `eus`).
-/

namespace Fragments.Basque

/-- Basque word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "eus"

end Fragments.Basque
