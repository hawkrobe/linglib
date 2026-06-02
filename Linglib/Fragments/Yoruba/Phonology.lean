import Linglib.Data.PHOIBLE.Inventories.Yoruba

/-!
# Yoruba phonological inventory
[moran-mccloy-2019]

Canonical PHOIBLE 2.0 phoneme inventory for Yoruba (ISO `yor`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Data/PHOIBLE/Inventories/Yoruba.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Yoruba.Phonology

/-- Canonical Yoruba phoneme inventory: first PHOIBLE inventory for ISO `yor`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.Yoruba.yor

end Yoruba.Phonology
