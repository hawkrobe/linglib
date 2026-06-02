import Linglib.Features.Coordination

/-!
# Lango Coordination Morphemes
[noonan-1992] [haspelmath-2007]

Lango (Nilotic, Uganda) uses *kèdè* for both comitative ('with') and
conjunction ('and'). Classic AND-language in [stassen-2000]'s
classification with diachronic source from comitative. [haspelmath-2007]
(20) cites [noonan-1992]:163.

- *kèdè* — J, free, medial prepositive: "A kèdè B" = 'A and B' / 'A with B'

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.lango`).
-/

namespace Lango.Coordination

open Features.Coordination

/-- *kèdè* — J particle, also comitative marker. Free, prepositive medial.
    Diachronic source: comitative ('with') → coordinator ('and'). -/
def kede : CoordEntry :=
  { form := "kèdè", gloss := "and; with"
  , role := .j, boundness := .free
  , note := "comitative-derived; identical form for 'with' and 'and'" }

def allEntries : List CoordEntry := [kede]

end Lango.Coordination
