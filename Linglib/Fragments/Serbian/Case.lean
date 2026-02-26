import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy

/-!
# Serbian Case Inventory

Serbian has **7 cases**: NOM, ACC, GEN, DAT, LOC, INST, VOC.
The standard Slavic 7-case system. The 6-case core (excluding VOC)
is perfectly contiguous on Blake's hierarchy.

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press.
-/

namespace Fragments.Serbian.Case

/-- Serbian 6-case core inventory (excluding VOC). -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .inst]

theorem inventory_valid :
    Core.validInventory caseInventory = true := by native_decide

end Fragments.Serbian.Case
