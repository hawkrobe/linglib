import Linglib.Typology.WordOrder

/-!
# Hixkaryana word-order profile

WALS-derived word-order profile for Hixkaryana (ISO `hix`). Hixkaryana is
one of the few documented OVS languages.
-/

namespace Fragments.Hixkaryana

/-- Hixkaryana word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "hix"

end Fragments.Hixkaryana
