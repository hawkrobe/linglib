import Linglib.Syntax.Category.Adposition.Order

/-!
# Japanese adposition order

WALS-derived adposition order for Japanese (ISO `jpn`). WALS Ch 85
classifies Japanese as postpositional.
-/

namespace Japanese

/-- Japanese adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "jpn"

end Japanese
