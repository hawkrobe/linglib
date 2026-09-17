import Linglib.Syntax.Negation

/-!
# Czech negation

Czech negates a clause with the verbal prefix *ne-*, attached directly to the finite verb or
auxiliary (*nejí* 'does not eat', *nebude jíst* 'will not eat') with no change of finiteness
or tense: symmetric negation in the sense of [miestamo-2005]. Negative concord is obligatory
and strict ([haspelmath-2013]), every *ni-* item co-occurring with the prefix; the items live
in the sibling `PolarityItems.lean`.

## References

* [miestamo-2005]
* [haspelmath-2013]
-/

namespace Czech.Negation

open Syntax.Negation

/-- *ne-*, the standard negation prefix. -/
def ne : Marker := { pieces := [[.pref "ne"]] }

end Czech.Negation
