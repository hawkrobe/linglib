import Linglib.Semantics.Coordination.Defs

/-!
# Kannada Coordination Morphemes
[sridhar-1990] [haspelmath-2007]

Kannada (Dravidian, India) uses the postpositive enclitic *-u* (often *-ū*)
on each coordinand for conjunction (A-co B-co), bisyndetic postpositive.
The same morpheme is the Dravidian additive/focus particle ('also').
[haspelmath-2007] (5) cites [sridhar-1990]:106.

- *-u* — MU, bound enclitic, additive: "Narahari-u Somashekhara-u" = 'N and S'

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.kannada`).
-/

namespace Kannada.Coordination

/-- *-u* — MU particle, also additive/focus. Bound enclitic, postpositive
    on each coordinand giving the bisyndetic A-co B-co pattern. -/
def u : Coordinator :=
  { form := "-u", gloss := "and; also"
  , role := .mu, kind := .bound .after .clitic, alsoAdditive := true
  , note := "bisyndetic postpositive enclitic; Dravidian additive particle" }

def allEntries : List Coordinator := [u]

end Kannada.Coordination
