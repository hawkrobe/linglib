import Linglib.Typology.WordOrder

/-!
# Turkish word-order profile

WALS-derived word-order profile for Turkish (ISO `tur`).
-/

namespace Fragments.Turkish

/-- Turkish word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "tur"

end Fragments.Turkish
