import Linglib.Syntax.Adposition.Order

/-!
# Hixkaryana adposition order

WALS-derived adposition order for Hixkaryana (ISO `hix`). WALS Ch 85
classifies Hixkaryana as postpositional.
-/

namespace Hixkaryana

/-- Hixkaryana adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "hix"

end Hixkaryana
