import Linglib.Typology.Adposition

/-!
# Mandarin adposition order

WALS-derived adposition order for Mandarin (ISO `cmn`). WALS Ch 85
classifies Mandarin as having both prepositions and postpositions
(no dominant order).
-/

namespace Fragments.Mandarin

/-- Mandarin adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "cmn"

end Fragments.Mandarin
