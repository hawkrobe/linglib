import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy

/-!
# Turkish Case Inventory @cite{blake-1994}
@cite{gksel-kerslake-2005} @cite{goksel-kerslake-2005}

Turkish has **6 cases** with agglutinative suffixes (Blake 1994, §5.4):
NOM (∅), ACC (-I), GEN (-In), DAT (-A), LOC (-DA), ABL (-DAn).

This inventory is perfectly contiguous on Blake's hierarchy: ranks 6–2
with no gaps. Turkish is the typological ideal case for the hierarchy —
a rich peripheral inventory built up exactly in the predicted order.

-/

namespace Fragments.Turkish.Case

/-- Turkish case inventory: NOM(∅), ACC(-I), GEN(-In), DAT(-A),
    LOC(-DA), ABL(-DAn). -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .abl]

/-- Perfectly contiguous on Blake's hierarchy (ranks 6, 6, 5, 4, 3, 2). -/
theorem inventory_valid :
    Core.validInventory caseInventory = true := by native_decide

end Fragments.Turkish.Case
