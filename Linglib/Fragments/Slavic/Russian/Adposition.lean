import Linglib.Typology.Adposition

/-!
# Russian adposition order

WALS-derived adposition order for Russian (ISO `rus`). WALS Ch 85
classifies Russian as prepositional.
-/

namespace Russian

/-- Russian adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "rus"

end Russian
