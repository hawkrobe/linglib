import Linglib.Core.Case

/-!
# Greek Case Inventory @cite{blake-1994}

Modern Greek has **4 cases**: NOM, ACC, GEN, VOC. The dative was lost
during the Koine period (1st c. BCE – 4th c. CE), with its functions
absorbed by the accusative and genitive (with prepositions).

Classical Greek had 5 cases (NOM, ACC, GEN, DAT, VOC), and Ancient
Greek arguably had traces of a locative and instrumental merged into
the dative.

The Modern Greek system (excluding VOC) is the minimal "inner
peripheral" inventory: core cases + genitive.

-/

namespace Fragments.Greek.Case

/-- Modern Greek 3-case inventory (excluding VOC). -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen]

-- Contiguous on Blake's hierarchy (ranks 6, 6, 5).
#guard Core.validInventory caseInventory

/-- Classical Greek with dative. -/
def classicalInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat]

#guard Core.validInventory classicalInventory

end Fragments.Greek.Case
