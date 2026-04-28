import Linglib.Typology.WordOrder

/-!
# Mandarin word-order profile

WALS-derived word-order profile for Mandarin (ISO `cmn`). Pure pass-through
of `WordOrderProfile.ofWALS "cmn"`.
-/

namespace Fragments.Mandarin

/-- Mandarin word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "cmn"

end Fragments.Mandarin
