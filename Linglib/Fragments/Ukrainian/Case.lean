import Linglib.Core.Case

/-!
# Ukrainian Case Inventory
@cite{blake-1994}

Ukrainian has **7 cases**: NOM, ACC, GEN, DAT, LOC, INST, VOC.
The standard Slavic 7-case system. The 6-case core (excluding VOC)
is perfectly contiguous on Blake's hierarchy.

-/

namespace Fragments.Ukrainian.Case

/-- Ukrainian 6-case core inventory (excluding VOC). -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .inst]

#guard Core.validInventory caseInventory

end Fragments.Ukrainian.Case
