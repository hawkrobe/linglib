import Linglib.Typology.WordOrder

/-!
# Russian word-order profile

WALS-derived word-order profile for Russian (ISO `rus`).
-/

namespace Fragments.Slavic.Russian

/-- Russian word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "rus"

end Fragments.Slavic.Russian
