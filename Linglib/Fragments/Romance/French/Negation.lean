import Linglib.Syntax.Negation

/-!
# French negation

French negates a clause with the proclitic *ne* before the finite verb and *pas* after it:
*jean vient* 'Jean comes', *jean ne vient pas* 'Jean does not come'. Nothing else in the clause
changes. *Ne* is regularly dropped in colloquial speech, leaving *pas* as the only negator. On
its own, without *pas*, *ne* occurs expletively under *avoir peur* 'fear', *avant que* 'before',
*à moins que* 'unless' and other triggers; the examples of [jin-koenig-2021] are the rows of
`Data.Examples.JinKoenig2021`. The pairs below are those of [miestamo-2005].

## References

* [miestamo-2005]
* [jin-koenig-2021]
-/

open Negation Morphology

namespace French.Negation

/-- *ne … pas*, the standard negator. -/
def nePas : Marker := { pieces := [[.procl "ne"], [.free "pas"]] }

/-- *ne* alone, the expletive negator. -/
def ne : Marker := { pieces := [[.procl "ne"]] }

/-- The present and the compound past of *venir* 'come'. -/
def pairs : List Pair :=
  [⟨[.free "jean", .free "vient"], [.free "jean", .procl "ne", .free "vient", .free "pas"]⟩,
   ⟨[.free "jean", .free "est", .root "ven", .suff "u"],
    [.free "jean", .procl "ne", .free "est", .free "pas", .root "ven", .suff "u"]⟩]

end French.Negation
