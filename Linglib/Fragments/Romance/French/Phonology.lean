import Linglib.Data.PHOIBLE.Inventories.French

/-!
# French phonological inventory
[moran-mccloy-2019]

Canonical PHOIBLE 2.0 phoneme inventory for French (ISO `fra`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Data/PHOIBLE/Inventories/French.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace French.Phonology

/-- Canonical French phoneme inventory: first PHOIBLE inventory for ISO `fra`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.French.fra

end French.Phonology
