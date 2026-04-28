import Linglib.Typology.Adposition

/-!
# Japanese adposition order

WALS-derived adposition order for Japanese (ISO `jpn`). WALS Ch 85
classifies Japanese as postpositional.
-/

namespace Fragments.Japanese

/-- Japanese adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "jpn"

end Fragments.Japanese
