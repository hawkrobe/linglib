import Linglib.Data.PHOIBLE.Inventories.HindiUrdu

/-!
# HindiUrdu phonological inventory
[moran-mccloy-2019]

Canonical PHOIBLE 2.0 phoneme inventory for HindiUrdu (ISO `hin`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Data/PHOIBLE/Inventories/HindiUrdu.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace HindiUrdu.Phonology

/-- Canonical HindiUrdu phoneme inventory: first PHOIBLE inventory for ISO `hin`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.HindiUrdu.hin

end HindiUrdu.Phonology
