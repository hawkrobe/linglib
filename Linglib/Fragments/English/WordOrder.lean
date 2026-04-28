import Linglib.Typology.WordOrder

/-!
# English word-order profile

WALS-derived word-order profile for English (ISO `eng`). Pure pass-through
of `WordOrderProfile.ofWALS "eng"` — see `Typology/WordOrder.lean` for the
underlying WALS Ch 81/82/83 lookup logic.
-/

namespace Fragments.English

/-- English word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "eng"

end Fragments.English
