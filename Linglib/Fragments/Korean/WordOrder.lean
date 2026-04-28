import Linglib.Typology.WordOrder

/-!
# Korean word-order profile

WALS-derived word-order profile for Korean (ISO `kor`).
-/

namespace Fragments.Korean

/-- Korean word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "kor"

end Fragments.Korean
