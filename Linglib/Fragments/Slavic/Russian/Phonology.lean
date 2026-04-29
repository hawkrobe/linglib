import Linglib.Datasets.PHOIBLE.Inventories.Russian

/-!
# Russian phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for Russian (ISO `rus`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Datasets/PHOIBLE/Inventories/Russian.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Fragments.Slavic.Russian.Phonology

/-- Canonical Russian phoneme inventory: first PHOIBLE inventory for ISO `rus`. -/
def phonemeInventory : Datasets.PHOIBLE.Inventory :=
  Datasets.PHOIBLE.Inventories.Russian.rus

end Fragments.Slavic.Russian.Phonology
