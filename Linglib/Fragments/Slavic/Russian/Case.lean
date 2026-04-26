import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Russian Case Inventory @cite{blake-1994}

Russian has **6 cases**: NOM, ACC, GEN, DAT, INST, LOC (prepositional).
No distinct vocative in standard Russian (unlike Ukrainian, Czech, Polish).

The inventory is perfectly contiguous on Blake's hierarchy.

For @cite{pesetsky-2013}'s POS-as-case reduction over the four core
cases (NOM=D, ACC=V, GEN=N, DAT=P), see
`Phenomena.Case.Studies.Pesetsky2013`, which imports this fragment.

-/

namespace Fragments.Slavic.Russian.Case

/-- Russian 6-case inventory. -/
def caseInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .inst, .loc}

-- Contiguous on Blake's hierarchy (ranks 6, 6, 5, 4, 2, 3).
example : Core.Case.IsValidInventory caseInventory := by decide

end Fragments.Slavic.Russian.Case
