import Linglib.Typology.Adposition

/-!
# English adposition order

WALS-derived adposition order for English (ISO `eng`). Pure pass-through
of `Typology.Adposition.adpositionOfWALS "eng"`. WALS Ch 85 classifies
English as prepositional.
-/

namespace Fragments.English

/-- English adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Option Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.adpositionOfWALS "eng"

end Fragments.English
