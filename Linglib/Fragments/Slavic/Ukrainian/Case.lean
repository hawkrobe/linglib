import Linglib.Fragments.Slavic.Case

/-!
# Ukrainian Case Inventory
[shevelov-1993] [blake-1994]

Per [shevelov-1993] (p. 956), Ukrainian preserves the original
6-case set (NOM/ACC/GEN/DAT/INST/LOC) and additionally retains a
productive vocative — robust in the singular (батько → батьку,
син → сину, хлопець → хлопче), eroded in the plural except for
панове/panove 'gentlemen'. `caseInventory` aliases the shared 6-case
core; `Slavic.Case.sevenCaseInventory` carries the +VOC form.
-/

namespace Ukrainian.Case

abbrev caseInventory : Finset Features.Case := Slavic.Case.coreInventory

end Ukrainian.Case
