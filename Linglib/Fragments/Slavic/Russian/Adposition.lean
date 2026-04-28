import Linglib.Typology.Adposition

/-!
# Russian adposition order

WALS-derived adposition order for Russian (ISO `rus`). WALS Ch 85
classifies Russian as prepositional.
-/

namespace Fragments.Slavic.Russian

/-- Russian adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "rus"

end Fragments.Slavic.Russian
