import Linglib.Typology.WordOrder

/-!
# Welsh word-order profile

WALS-derived word-order profile for Welsh (ISO `cym`).
-/

namespace Fragments.Welsh

/-- Welsh word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "cym"

end Fragments.Welsh
