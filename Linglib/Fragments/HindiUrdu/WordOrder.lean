import Linglib.Typology.WordOrder

/-!
# Hindi/Urdu word-order profile

WALS-derived word-order profile for Hindi (ISO `hin`).
-/

namespace Fragments.HindiUrdu

/-- Hindi word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "hin"

end Fragments.HindiUrdu
