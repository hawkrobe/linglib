import Linglib.Datasets.PHOIBLE.Inventories.Yoruba

/-!
# Yoruba phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for Yoruba (ISO `yor`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Datasets/PHOIBLE/Inventories/Yoruba.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Fragments.Yoruba.Phonology

/-- Canonical Yoruba phoneme inventory: first PHOIBLE inventory for ISO `yor`. -/
def phonemeInventory : Datasets.PHOIBLE.Inventory :=
  Datasets.PHOIBLE.Inventories.Yoruba.yor

end Fragments.Yoruba.Phonology
