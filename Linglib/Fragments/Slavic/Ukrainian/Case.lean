import Linglib.Fragments.Slavic.Case

/-!
# Ukrainian Case Inventory
@cite{shevelov-1993} @cite{blake-1994}

Per @cite{shevelov-1993} (p. 956), Ukrainian preserves the original
6-case set (NOM/ACC/GEN/DAT/INST/LOC) and additionally retains a
productive vocative — robust in the singular (батько → батьку,
син → сину, хлопець → хлопче), eroded in the plural except for
панове/panove 'gentlemen'. `caseInventory` aliases the shared 6-case
core; `Fragments.Slavic.Case.sevenCaseInventory` carries the +VOC form.
-/

namespace Fragments.Slavic.Ukrainian.Case

abbrev caseInventory : Finset Core.Case := Fragments.Slavic.Case.coreInventory

end Fragments.Slavic.Ukrainian.Case
