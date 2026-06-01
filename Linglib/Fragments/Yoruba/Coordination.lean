import Linglib.Features.Coordination

/-!
# Yoruba Coordination Morphemes
@cite{rowlands-1969} @cite{haspelmath-2007}

Yoruba (Kwa, Nigeria) shows canonical prepositive bisyndetic coordination
(*àtí A àtí B*). @cite{haspelmath-2007} (25) cites @cite{rowlands-1969}:201ff.

- *àtí* — J, free, prepositive on each conjunct (bisyndetic A-co B-co)

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.yoruba`).
-/

namespace Yoruba.Coordination

open Features.Coordination

/-- *àtí* — J particle, used bisyndetically: "àtí A àtí B". Free, prepositive. -/
def ati : CoordEntry :=
  { form := "àtí", gloss := "and"
  , role := .j, boundness := .free
  , correlative := true
  , note := "bisyndetic prepositive (co-A co-B pattern)" }

def allEntries : List CoordEntry := [ati]

end Yoruba.Coordination
