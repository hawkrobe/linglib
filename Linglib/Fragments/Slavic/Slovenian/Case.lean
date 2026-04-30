import Linglib.Fragments.Slavic.Case

/-!
# Slovene Case Inventory
@cite{priestly-1993} @cite{blake-1994}

Per @cite{priestly-1993} (p. 399), Slovene has 6 cases
(NOM/ACC/GEN/DAT/INST/LOC) with no productive vocative, patterning
with standard Russian against Ukrainian/Polish/Czech/Serbo-Croat among
the modern Slavic case-bearing languages. The prepositional
restriction Priestly notes for INST is Slovene-specific within Slavic
(see `Fragments/Slavic/Case.lean` for cross-Slavic discussion). The
directory name `Slovenian` is historical; Priestly's chapter title is
"Slovene".
-/

namespace Fragments.Slavic.Slovenian.Case

abbrev caseInventory : Finset Core.Case := Fragments.Slavic.Case.coreInventory

end Fragments.Slavic.Slovenian.Case
