import Linglib.Typology.Adposition

/-!
# Hixkaryana adposition order

WALS-derived adposition order for Hixkaryana (ISO `hix`). WALS Ch 85
classifies Hixkaryana as postpositional.
-/

namespace Fragments.Hixkaryana

/-- Hixkaryana adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "hix"

end Fragments.Hixkaryana
