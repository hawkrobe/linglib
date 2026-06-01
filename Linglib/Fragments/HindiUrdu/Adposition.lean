import Linglib.Typology.Adposition

/-!
# Hindi/Urdu adposition order

WALS-derived adposition order for Hindi (ISO `hin`). WALS Ch 85
classifies Hindi as postpositional.
-/

namespace HindiUrdu

/-- Hindi adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "hin"

end HindiUrdu
