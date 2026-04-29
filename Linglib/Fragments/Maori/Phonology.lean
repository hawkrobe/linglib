import Linglib.Datasets.PHOIBLE.Inventories.Maori

/-!
# Maori phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for Maori (ISO `mri`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Datasets/PHOIBLE/Inventories/Maori.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Fragments.Maori.Phonology

/-- Canonical Maori phoneme inventory: first PHOIBLE inventory for ISO `mri`. -/
def phonemeInventory : Datasets.PHOIBLE.Inventory :=
  Datasets.PHOIBLE.Inventories.Maori.mri

end Fragments.Maori.Phonology
