import Linglib.Core.Case
import Linglib.Theories.Morphology.CaseContainment
open Theories.Morphology.CaseContainment

/-!
# German Case Inventory @cite{blake-1994}

German has **4 cases**: NOM, ACC, GEN, DAT. This is the largest contiguous
inventory possible without any peripheral (spatial) cases — exactly the
"inner peripheral" boundary on Blake's hierarchy.

## Syncretism

German has extensive syncretism, especially in the definite article:
- NOM/ACC syncretism: neuter and feminine (der/das/die paradigm)
- DAT/GEN syncretism: rare but occurs in some dialects

-/

namespace Fragments.German.Case

/-- German 4-case inventory. -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat]

-- Contiguous on Blake's hierarchy (ranks 6, 6, 5, 4).
#guard Core.validInventory caseInventory

/-- NOM/ACC syncretism in neuter and feminine.
    Instantiates the cross-linguistic NOM/ACC pattern from `Core.Case.Syncretism`. -/
def neuterSyncretism : Syncretism := nomAccSyncretism

end Fragments.German.Case
