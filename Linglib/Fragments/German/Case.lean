import Linglib.Features.Case.Basic

/-!
# German Case Inventory [blake-1994]

German has **4 cases**: NOM, ACC, GEN, DAT. This is the largest contiguous
inventory possible without any peripheral (spatial) cases — exactly the
"inner peripheral" boundary on Blake's hierarchy.

## Syncretism

German has extensive syncretism, especially in the definite article:
- NOM/ACC syncretism: neuter and feminine (der/das/die paradigm)
- DAT/GEN syncretism: rare but occurs in some dialects

-/

namespace German.Case

/-- German 4-case inventory. -/
def caseInventory : Finset Case :=
  {.nom, .acc, .gen, .dat}

-- Contiguous on Blake's hierarchy (ranks 6, 6, 5, 4).
example : Case.IsValidInventory caseInventory := by decide

end German.Case
