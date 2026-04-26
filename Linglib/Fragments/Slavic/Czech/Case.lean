import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Czech Case Inventory
@cite{blake-1994}

Czech has **7 cases**: NOM, ACC, GEN, DAT, LOC, INST, VOC.
The standard Slavic 7-case system. VOC is marginal (rank 0) and outside
Blake's main hierarchy; the 6-case core is perfectly contiguous.

-/

namespace Fragments.Slavic.Czech.Case

/-- Czech 6-case core inventory (excluding VOC). -/
def caseInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst}

-- Contiguous on Blake's hierarchy (ranks 6, 6, 5, 4, 3, 2).
example : Core.Case.IsValidInventory caseInventory := by decide

end Fragments.Slavic.Czech.Case
