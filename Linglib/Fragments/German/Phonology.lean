import Linglib.Datasets.PHOIBLE.Inventories.German

/-!
# German phonological inventory
@cite{moran-mccloy-2019}

Canonical PHOIBLE 2.0 phoneme inventory for German (ISO `deu`). Pure
pass-through to the auto-generated PHOIBLE doculect data in
`Datasets/PHOIBLE/Inventories/German.lean`.

The choice of which PHOIBLE inventory to treat as canonical (PHOIBLE has
multiple doculects per ISO) is made here at the Fragment layer, so
downstream Studies access the inventory via this Fragment rather than
naming a PHOIBLE InventoryID directly.
-/

namespace Fragments.German.Phonology

/-- Canonical German phoneme inventory: first PHOIBLE inventory for ISO `deu`. -/
def phonemeInventory : Datasets.PHOIBLE.Inventory :=
  Datasets.PHOIBLE.Inventories.German.deu

end Fragments.German.Phonology
