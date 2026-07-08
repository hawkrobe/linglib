import Linglib.Syntax.Category.Adposition.Order

/-!
# Hindi/Urdu adposition order

WALS-derived adposition order for Hindi (ISO `hin`). WALS Ch 85
classifies Hindi as postpositional.
-/

namespace HindiUrdu

/-- Hindi adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "hin"

end HindiUrdu
