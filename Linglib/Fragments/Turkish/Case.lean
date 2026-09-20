import Linglib.Syntax.Case.Basic

/-!
# Turkish Case Inventory [blake-1994]
[goksel-kerslake-2005]

Turkish has **6 cases** with agglutinative suffixes:
NOM (∅), ACC (-I), GEN (-In), DAT (-A), LOC (-DA), ABL (-DAn).

The instrumental function is expressed by a postposition. [blake-1994] cites the
system for the ablative stage of his hierarchy (`Studies/Blake1994.lean`).

-/

namespace Turkish.Case

/-- Turkish case inventory: NOM(∅), ACC(-I), GEN(-In), DAT(-A),
    LOC(-DA), ABL(-DAn). -/
def inventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc, .abl}

end Turkish.Case
