import Linglib.Typology.Adposition

/-!
# Japanese adposition order

WALS-derived adposition order for Japanese (ISO `jpn`). WALS Ch 85
classifies Japanese as postpositional.
-/

namespace Japanese

/-- Japanese adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "jpn"

end Japanese
