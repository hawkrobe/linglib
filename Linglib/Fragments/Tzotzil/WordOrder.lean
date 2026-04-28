import Linglib.Typology.WordOrder

/-!
# Tzotzil word-order profile

WALS-derived word-order profile for Tzotzil (ISO `tzo`).
-/

namespace Fragments.Tzotzil

/-- Tzotzil word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "tzo"

end Fragments.Tzotzil
