import Linglib.Data.PHOIBLE.Inventories.Japanese

/-!
# Japanese phonological inventory
[moran-mccloy-2019]

Canonical PHOIBLE 2.0 phoneme inventory for Japanese (ISO `jpn`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Data/PHOIBLE/Inventories/Japanese.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Japanese.Phonology

/-- Canonical Japanese phoneme inventory: first PHOIBLE inventory for ISO `jpn`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.Japanese.jpn

end Japanese.Phonology
