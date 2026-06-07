import Linglib.Fragments.Slavic.Case

/-!
# Slovene Case Inventory
[priestly-1993] [blake-1994]

Per [priestly-1993] (p. 399), Slovene has 6 cases
(NOM/ACC/GEN/DAT/INST/LOC) with no productive vocative, patterning
with standard Russian against Ukrainian/Polish/Czech/Serbo-Croat among
the modern Slavic case-bearing languages. The prepositional
restriction Priestly notes for INST is Slovene-specific within Slavic
(see `Fragments/Slavic/Case.lean` for cross-Slavic discussion). The
directory name `Slovenian` is historical; Priestly's chapter title is
"Slovene".
-/

namespace Slovenian.Case

abbrev caseInventory : Finset Case := Slavic.Case.coreInventory

end Slovenian.Case
