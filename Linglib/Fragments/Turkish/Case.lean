import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Turkish Case Inventory @cite{blake-1994}
@cite{goksel-kerslake-2005}

Turkish has **6 cases** with agglutinative suffixes:
NOM (∅), ACC (-I), GEN (-In), DAT (-A), LOC (-DA), ABL (-DAn).

This inventory is perfectly contiguous on Blake's hierarchy: ranks 6–2
with no gaps. Turkish is the typological ideal case for the hierarchy —
a rich peripheral inventory built up exactly in the predicted order.

-/

namespace Fragments.Turkish.Case

/-- Turkish case inventory: NOM(∅), ACC(-I), GEN(-In), DAT(-A),
    LOC(-DA), ABL(-DAn). -/
def caseInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .loc, .abl}

-- Perfectly contiguous on Blake's hierarchy (ranks 6, 6, 5, 4, 3, 2).
example : Core.Case.IsValidInventory caseInventory := by decide

end Fragments.Turkish.Case
