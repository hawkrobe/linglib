import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Polish Case Inventory
@cite{blake-1994}

Polish has **7 cases**: NOM, ACC, GEN, DAT, LOC, INST, VOC.
The standard Slavic 7-case system. The 6-case core (excluding VOC)
is perfectly contiguous on Blake's hierarchy.

-/

namespace Fragments.Slavic.Polish.Case

/-- Polish 6-case core inventory (excluding VOC). -/
def caseInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst}

example : Core.Case.IsValidInventory caseInventory := by decide

end Fragments.Slavic.Polish.Case
