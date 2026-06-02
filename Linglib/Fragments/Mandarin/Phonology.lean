import Linglib.Data.PHOIBLE.Inventories.MandarinChinese

/-!
# Mandarin phonological inventory
[moran-mccloy-2019]

Canonical PHOIBLE 2.0 phoneme inventory for Mandarin (ISO `cmn`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Data/PHOIBLE/Inventories/MandarinChinese.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Mandarin.Phonology

/-- Canonical Mandarin phoneme inventory: first PHOIBLE inventory for ISO `cmn`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.MandarinChinese.cmn

end Mandarin.Phonology
