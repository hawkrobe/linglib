import Linglib.Typology.WordOrder

/-!
# Irish word-order profile

WALS-derived word-order profile for Irish (ISO `gle`).
-/

namespace Fragments.Irish

/-- Irish word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "gle"

end Fragments.Irish
