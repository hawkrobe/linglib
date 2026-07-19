import Linglib.Semantics.Coordination.Defs

/-!
# Persian (Farsi) Coordination Morphemes
[haspelmath-2007] [mitrovic-sauerland-2016]

Persian has:

- *va* — J, free, prepositive: "A va B" (Arabic-origin loan; colloquial *o*)
- *ham* — MU, free, additive ('also'): "A ham B ham" — bisyndetic

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.persian`).
-/

namespace Farsi.Coordination

/-- *va* — J particle (Arabic loan; colloquial enclitic *o*). Free, prepositive. -/
def va : Coordinator :=
  { form := "va", gloss := "and"
  , role := .j, kind := .free
  , note := "Arabic-origin loan; colloquial enclitic 'o'" }

/-- *ham* — MU particle, also additive. Free, used bisyndetically. -/
def ham : Coordinator :=
  { form := "ham", gloss := "also, too; and (MU)"
  , role := .mu, kind := .free, alsoAdditive := true
  , correlative := true }

def allEntries : List Coordinator := [va, ham]

end Farsi.Coordination
