import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Serbian Case Inventory
@cite{blake-1994}

Serbian has **7 cases**: NOM, ACC, GEN, DAT, LOC, INST, VOC.
The standard Slavic 7-case system. The 6-case core (excluding VOC)
is perfectly contiguous on Blake's hierarchy.

-/

namespace Fragments.Slavic.Serbian.Case

/-- Serbian 6-case core inventory (excluding VOC). -/
def caseInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst}

example : Core.Case.IsValidInventory caseInventory := by decide

end Fragments.Slavic.Serbian.Case
