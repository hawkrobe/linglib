import Linglib.Fragments.Slavic.Case

/-!
# Russian Case Inventory
[timberlake-1993] [blake-1994] [pesetsky-2013]

Per [timberlake-1993] (p. 836), Russian has 6 primary cases
(NOM/ACC/GEN/DAT/INST/LOC) and 2 secondary cases (second GEN, second
LOC) used by a small and shrinking class of masculines; the historical
vocative is moribund. `caseInventory` aliases the shared 6-case core
(secondary cases are paradigm slots within selected nouns, not modeled
at the inventory level). For [pesetsky-2013]'s POS-as-case
reduction, see `Pesetsky2013`.
-/

namespace Russian.Case

abbrev caseInventory : Finset Features.Case := Slavic.Case.coreInventory

end Russian.Case
