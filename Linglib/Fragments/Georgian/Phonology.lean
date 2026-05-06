import Linglib.Data.PHOIBLE.Inventories.Georgian

/-!
# Georgian phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for Georgian (ISO `kat`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Data/PHOIBLE/Inventories/Georgian.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Fragments.Georgian.Phonology

/-- Canonical Georgian phoneme inventory: first PHOIBLE inventory for ISO `kat`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.Georgian.kat

end Fragments.Georgian.Phonology
