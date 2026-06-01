import Linglib.Features.Coordination

/-!
# Lango Coordination Morphemes
@cite{noonan-1992} @cite{haspelmath-2007}

Lango (Nilotic, Uganda) uses *kèdè* for both comitative ('with') and
conjunction ('and'). Classic AND-language in @cite{stassen-2000}'s
classification with diachronic source from comitative. @cite{haspelmath-2007}
(20) cites @cite{noonan-1992}:163.

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
