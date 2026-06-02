import Linglib.Fragments.Slavic.Case

/-!
# Serbo-Croat Case Inventory
[browne-1993] [blake-1994]

Per [browne-1993] (p. 319), Serbo-Croat has a 7-case system with
productive VOC; DAT and LOC have merged in the noun paradigm except for
accentual distinctions in some monosyllables. `caseInventory` aliases
the shared 6-case core; `Slavic.Case.sevenCaseInventory`
carries the +VOC form. The directory name `Serbian` is historical;
Browne's chapter covers the unified Serbo-Croat standard.
-/

namespace Serbian.Case

abbrev caseInventory : Finset Features.Case := Slavic.Case.coreInventory

end Serbian.Case
