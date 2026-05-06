import Linglib.Data.PHOIBLE.Inventories.Zulu

/-!
# Zulu phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for Zulu (ISO `zul`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Data/PHOIBLE/Inventories/Zulu.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Fragments.Zulu.Phonology

/-- Canonical Zulu phoneme inventory: first PHOIBLE inventory for ISO `zul`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.Zulu.zul

end Fragments.Zulu.Phonology
