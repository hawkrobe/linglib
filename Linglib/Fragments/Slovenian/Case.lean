import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy

/-!
# Slovenian Case Inventory

Slovenian has **6 cases**: NOM, ACC, GEN, DAT, LOC, INST. Unlike
most other South Slavic languages (which have lost case), Slovenian
preserves the full 6-case system. No distinct vocative.

Perfectly contiguous on Blake's hierarchy.

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press.
-/

namespace Fragments.Slovenian.Case

/-- Slovenian 6-case inventory. -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .inst]

theorem inventory_valid :
    Core.validInventory caseInventory = true := by native_decide

end Fragments.Slovenian.Case
