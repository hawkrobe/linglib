import Linglib.Syntax.Adposition.Order

/-!
# English adposition order

WALS-derived adposition order for English (ISO `eng`). Pure pass-through
of `Adposition.AdpositionOrder.ofWALS "eng"`. WALS Ch 85 classifies
English as prepositional.
-/

namespace English

/-- English adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "eng"

end English
