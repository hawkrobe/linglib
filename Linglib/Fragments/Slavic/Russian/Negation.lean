import Linglib.Syntax.Negation

/-!
# Russian negation

Russian negates a clause with the preverbal particle *ne* (не), and nothing else in the clause
changes: *ja govor-ju po-russkij* 'I speak Russian', *ja ne govor-ju po-russkij* 'I do not speak
Russian'. Negative concord is obligatory, every item of the *ni-* series co-occurring with
*ne*; the items are entered in `Fragments/Slavic/Russian/PolarityItems.lean`. The example is
that of [miestamo-2005].

## References

* [miestamo-2005]
-/

open Negation Morphology

namespace Russian.Negation

/-- *ne* (не), the standard negator. -/
def ne : Marker := { pieces := [[.free "ne"]] }

/-- *ja govor-ju po-russkij* 'I speak Russian' and its negative. -/
def pairs : List Pair :=
  [⟨[.free "ja", .root "govor", .suff "ju", .free "po-russkij"],
    [.free "ja", .free "ne", .root "govor", .suff "ju", .free "po-russkij"]⟩]

end Russian.Negation
