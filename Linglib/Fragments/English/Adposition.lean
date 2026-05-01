import Linglib.Typology.Adposition

/-!
# English adposition order

WALS-derived adposition order for English (ISO `eng`). Pure pass-through
of `Typology.Adposition.AdpositionOrder.ofWALS "eng"`. WALS Ch 85 classifies
English as prepositional.
-/

namespace Fragments.English

/-- English adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Typology.Adposition.AdpositionOrder :=
  Typology.Adposition.AdpositionOrder.ofWALS "eng"

end Fragments.English
