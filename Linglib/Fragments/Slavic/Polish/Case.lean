import Linglib.Fragments.Slavic.Case

/-!
# Polish Case Inventory
[rothstein-1993] [blake-1994]

Per [rothstein-1993] (p. 696), Polish has the full inherited
7-case system including a productive vocative used consistently with
titles and vocative phrases (panie Janku, kochana Basiu), with a
growing tendency for NOM to substitute for VOC with bare personal
names. `inventory` aliases the shared 6-case core;
`Slavic.Case.fullInventory` carries the +VOC form.
-/

namespace Polish.Case

abbrev inventory : Finset Case := Slavic.Case.coreInventory

end Polish.Case
