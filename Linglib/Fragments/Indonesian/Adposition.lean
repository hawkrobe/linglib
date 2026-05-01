import Linglib.Typology.Adposition

/-!
# Indonesian adposition order

WALS-derived adposition order for Indonesian (ISO `ind`). WALS Ch 85
classifies Indonesian as prepositional.
-/

namespace Fragments.Indonesian

/-- Indonesian adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "ind"

end Fragments.Indonesian
