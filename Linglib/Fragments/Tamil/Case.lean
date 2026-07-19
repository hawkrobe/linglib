import Linglib.Features.Case.Basic
import Linglib.Features.Case.Basic

/-!
# Tamil Case Inventory
[blake-1994]

Tamil (Dravidian) has **8 cases** with agglutinative suffixes:
NOM (∅), ACC (-ai), DAT (-ukku), GEN (-in / -uṭaiya), LOC (-il),
ABL (-ilirundu), INST / COM (-āl / -ōṭu), VOC (-ē).

The instrumental and comitative are sometimes syncretic (-ōṭu covers
both functions), a pattern documented cross-linguistically ([blake-1994];
WALS Ch. 52).

-/

namespace Tamil.Case

/-- Tamil 7-case core inventory (excluding VOC). -/
def caseInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc, .abl, .inst, .com}

-- Contiguous on Blake's hierarchy (ranks 6 down to 1).
example : Case.IsValidInventory caseInventory := by decide

theorem com_inst_adjacent :
    Case.HierarchyAdjacent .com .inst := by decide

end Tamil.Case
