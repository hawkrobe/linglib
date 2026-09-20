import Linglib.Syntax.Case.Basic
/-!
# Greek Case Inventory [blake-1994]

Modern Greek has **4 cases**: NOM, ACC, GEN, VOC. The dative was lost
during the Koine period (1st c. BCE – 4th c. CE), with its functions
absorbed by the accusative and genitive (with prepositions).

Classical Greek had 5 cases (NOM, ACC, GEN, DAT, VOC), and Ancient
Greek arguably had traces of a locative and instrumental merged into
the dative.

The Modern Greek system (excluding VOC) is the minimal "inner
peripheral" inventory: core cases + genitive.

-/

namespace Greek.Case

/-- Modern Greek 3-case inventory (excluding VOC). -/
def inventory : Finset Case :=
  {.nom, .acc, .gen}

/-- Classical Greek with dative. -/
def classicalInventory : Finset Case :=
  {.nom, .acc, .gen, .dat}

end Greek.Case
