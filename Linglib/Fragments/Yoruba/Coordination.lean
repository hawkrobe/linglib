import Linglib.Semantics.Coordination.Defs

/-!
# Yoruba Coordination Morphemes
[rowlands-1969] [haspelmath-2007]

Yoruba (Kwa, Nigeria) shows canonical prepositive bisyndetic coordination
(*àtí A àtí B*). [haspelmath-2007] (25) cites [rowlands-1969]:201ff.

- *àtí* — J, free, prepositive on each conjunct (bisyndetic A-co B-co)

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.yoruba`).
-/

namespace Yoruba.Coordination

/-- *àtí* — J particle, used bisyndetically: "àtí A àtí B". Free, prepositive. -/
def ati : Coordinator :=
  { form := "àtí", gloss := "and"
  , role := .j, kind := .free
  , correlative := true
  , note := "bisyndetic prepositive (co-A co-B pattern)" }

def allEntries : List Coordinator := [ati]

end Yoruba.Coordination
