import Linglib.Core.Case

/-!
# Czech Case Inventory
@cite{blake-1994}

Czech has **7 cases**: NOM, ACC, GEN, DAT, LOC, INST, VOC.
The standard Slavic 7-case system. VOC is marginal (rank 0) and outside
Blake's main hierarchy; the 6-case core is perfectly contiguous.

-/

namespace Fragments.Czech.Case

/-- Czech 6-case core inventory (excluding VOC). -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .inst]

-- Contiguous on Blake's hierarchy (ranks 6, 6, 5, 4, 3, 2).
#guard Core.validInventory caseInventory

end Fragments.Czech.Case
