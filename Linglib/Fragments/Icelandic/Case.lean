import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Icelandic Case Inventory
@cite{thrainsson-2007}

Icelandic has **4 morphological cases**: NOM, ACC, DAT, GEN. Contiguous
on Blake's hierarchy (ranks 6, 6, 5, 4).

Case frames, quirky subjects, verb data, and agreement are in
`Icelandic/Verbs.lean`.
-/

namespace Fragments.Icelandic.Case

open Core

/-- Icelandic 4-case inventory (@cite{thrainsson-2007} §4.1). -/
def caseInventory : Finset Case := {.nom, .acc, .gen, .dat}

example : Case.IsValidInventory caseInventory := by decide

theorem icelandic_has_four_cases : caseInventory.card = 4 := by decide

end Fragments.Icelandic.Case
