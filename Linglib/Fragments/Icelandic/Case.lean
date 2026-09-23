import Linglib.Syntax.Case.Basic
/-!
# Icelandic Case Inventory
[thrainsson-2007]

Icelandic has **4 morphological cases**: NOM, ACC, DAT, GEN.

The case arrays of verbs are in `Icelandic/Verbs.lean`.
-/

namespace Icelandic.Case

/-- Icelandic 4-case inventory ([thrainsson-2007] §4.1). -/
def inventory : Finset Case := {.nom, .acc, .gen, .dat}

end Icelandic.Case
