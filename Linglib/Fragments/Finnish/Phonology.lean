import Linglib.Data.PHOIBLE.Inventories.Finnish

/-!
# Finnish phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for Finnish (ISO `fin`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Data/PHOIBLE/Inventories/Finnish.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Fragments.Finnish.Phonology

/-- Canonical Finnish phoneme inventory: first PHOIBLE inventory for ISO `fin`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.Finnish.fin

end Fragments.Finnish.Phonology
