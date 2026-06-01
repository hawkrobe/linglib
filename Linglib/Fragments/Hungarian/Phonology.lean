import Linglib.Data.PHOIBLE.Inventories.Hungarian

/-!
# Hungarian phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for Hungarian (ISO `hun`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Data/PHOIBLE/Inventories/Hungarian.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Hungarian.Phonology

/-- Canonical Hungarian phoneme inventory: first PHOIBLE inventory for ISO `hun`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.Hungarian.hun

end Hungarian.Phonology
