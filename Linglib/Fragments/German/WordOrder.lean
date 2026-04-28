import Linglib.Typology.WordOrder

/-!
# German word-order profile

WALS-derived word-order profile for German (ISO `deu`). German is
classified as having no dominant word order in WALS Ch 81/83.
-/

namespace Fragments.German

/-- German word-order profile (WALS Ch 81/82/83 by ISO lookup). -/
def wordOrder : Typology.WordOrder.WordOrderProfile :=
  Typology.WordOrder.WordOrderProfile.ofWALS "deu"

end Fragments.German
