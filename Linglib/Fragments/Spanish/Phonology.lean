import Linglib.Datasets.PHOIBLE.Inventories.Spanish

/-!
# Spanish phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for Spanish (ISO `spa`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Datasets/PHOIBLE/Inventories/Spanish.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Fragments.Spanish.Phonology

/-- Canonical Spanish phoneme inventory: first PHOIBLE inventory for ISO `spa`. -/
def phonemeInventory : Datasets.PHOIBLE.Inventory :=
  Datasets.PHOIBLE.Inventories.Spanish.spa

end Fragments.Spanish.Phonology
