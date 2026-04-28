import Linglib.Typology.WordOrder

/-!
# Japanese word-order profile

WALS-derived word-order profile for Japanese (ISO `jpn`). Pure pass-through
of `WordOrderProfile.ofWALS "jpn"`.
-/

namespace Fragments.Japanese

/-- Japanese word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "jpn"

end Fragments.Japanese
