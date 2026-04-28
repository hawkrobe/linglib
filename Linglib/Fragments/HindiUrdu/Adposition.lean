import Linglib.Typology.Adposition

/-!
# Hindi/Urdu adposition order

WALS-derived adposition order for Hindi (ISO `hin`). WALS Ch 85
classifies Hindi as postpositional.
-/

namespace Fragments.HindiUrdu

/-- Hindi adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "hin"

end Fragments.HindiUrdu
