import Linglib.Fragments.Slavic.Case

/-!
# Polish Case Inventory
@cite{rothstein-1993} @cite{blake-1994}

Per @cite{rothstein-1993} (p. 696), Polish has the full inherited
7-case system including a productive vocative used consistently with
titles and vocative phrases (panie Janku, kochana Basiu), with a
growing tendency for NOM to substitute for VOC with bare personal
names. `caseInventory` aliases the shared 6-case core;
`Fragments.Slavic.Case.sevenCaseInventory` carries the +VOC form.
-/

namespace Fragments.Slavic.Polish.Case

abbrev caseInventory : Finset Features.Case := Fragments.Slavic.Case.coreInventory

end Fragments.Slavic.Polish.Case
