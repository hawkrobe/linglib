import Linglib.Typology.WordOrder

/-!
# Indonesian word-order profile

WALS-derived word-order profile for Indonesian (ISO `ind`).
-/

namespace Fragments.Indonesian

/-- Indonesian word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "ind"

end Fragments.Indonesian
