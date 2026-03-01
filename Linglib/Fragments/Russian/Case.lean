import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy

/-!
# Russian Case Inventory @cite{blake-1994}

Russian has **6 cases**: NOM, ACC, GEN, DAT, INST, LOC (prepositional).
No distinct vocative in standard Russian (unlike Ukrainian, Czech, Polish).

The inventory is perfectly contiguous on Blake's hierarchy.

-/

namespace Fragments.Russian.Case

/-- Russian 6-case inventory. -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .inst, .loc]

/-- Contiguous on Blake's hierarchy (ranks 6, 6, 5, 4, 2, 3). -/
theorem inventory_valid :
    Core.validInventory caseInventory = true := by native_decide

end Fragments.Russian.Case
