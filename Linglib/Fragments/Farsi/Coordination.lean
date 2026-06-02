import Linglib.Features.Coordination

/-!
# Persian (Farsi) Coordination Morphemes
[haspelmath-2007] [mitrovic-sauerland-2016]

Persian has:

- *va* — J, free, prepositive: "A va B" (Arabic-origin loan; colloquial *o*)
- *ham* — MU, free, additive ('also'): "A ham B ham" — bisyndetic

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.persian`).
-/

namespace Farsi.Coordination

open Features.Coordination

/-- *va* — J particle (Arabic loan; colloquial enclitic *o*). Free, prepositive. -/
def va : CoordEntry :=
  { form := "va", gloss := "and"
  , role := .j, boundness := .free
  , note := "Arabic-origin loan; colloquial enclitic 'o'" }

/-- *ham* — MU particle, also additive. Free, used bisyndetically. -/
def ham : CoordEntry :=
  { form := "ham", gloss := "also, too; and (MU)"
  , role := .mu, boundness := .free, alsoAdditive := true
  , correlative := true }

def allEntries : List CoordEntry := [va, ham]

end Farsi.Coordination
