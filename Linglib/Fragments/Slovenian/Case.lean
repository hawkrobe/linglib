import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Slovenian Case Inventory
@cite{blake-1994}

Slovenian has **6 cases**: NOM, ACC, GEN, DAT, LOC, INST. Unlike
most other South Slavic languages (which have lost case), Slovenian
preserves the full 6-case system. No distinct vocative.

Perfectly contiguous on Blake's hierarchy.

-/

namespace Fragments.Slovenian.Case

/-- Slovenian 6-case inventory. -/
def caseInventory : Finset Core.Case :=
  {.nom, .acc, .gen, .dat, .loc, .inst}

example : Core.Case.IsValidInventory caseInventory := by decide

end Fragments.Slovenian.Case
