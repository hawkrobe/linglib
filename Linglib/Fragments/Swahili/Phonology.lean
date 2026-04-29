import Linglib.Datasets.PHOIBLE.Inventories.Swahili

/-!
# Swahili phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for Swahili (ISO `swh`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Datasets/PHOIBLE/Inventories/Swahili.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Fragments.Swahili.Phonology

/-- Canonical Swahili phoneme inventory: first PHOIBLE inventory for ISO `swh`. -/
def phonemeInventory : Datasets.PHOIBLE.Inventory :=
  Datasets.PHOIBLE.Inventories.Swahili.swh

end Fragments.Swahili.Phonology
