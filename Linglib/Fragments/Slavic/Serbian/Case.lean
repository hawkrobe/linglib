import Linglib.Fragments.Slavic.Case

/-!
# Serbo-Croat Case Inventory
@cite{browne-1993} @cite{blake-1994}

Per @cite{browne-1993} (p. 319), Serbo-Croat has a 7-case system with
productive VOC; DAT and LOC have merged in the noun paradigm except for
accentual distinctions in some monosyllables. `caseInventory` aliases
the shared 6-case core; `Fragments.Slavic.Case.sevenCaseInventory`
carries the +VOC form. The directory name `Serbian` is historical;
Browne's chapter covers the unified Serbo-Croat standard.
-/

namespace Fragments.Slavic.Serbian.Case

abbrev caseInventory : Finset Core.Case := Fragments.Slavic.Case.coreInventory

end Fragments.Slavic.Serbian.Case
