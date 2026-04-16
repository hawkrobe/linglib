import Linglib.Core.Case
import Linglib.Theories.Morphology.CaseContainment
open Morphology.CaseContainment

/-!
# Tamil Case Inventory
@cite{blake-1994}

Tamil (Dravidian) has **8 cases** with agglutinative suffixes:
NOM (∅), ACC (-ai), DAT (-ukku), GEN (-in / -uṭaiya), LOC (-il),
ABL (-ilirundu), INST / COM (-āl / -ōṭu), VOC (-ē).

The instrumental and comitative are sometimes syncretic (-ōṭu covers
both functions), a pattern documented cross-linguistically (@cite{blake-1994};
WALS Ch. 52).

-/

namespace Fragments.Tamil.Case

/-- Tamil 7-case core inventory (excluding VOC). -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .abl, .inst, .com]

-- Contiguous on Blake's hierarchy (ranks 6 down to 1).
#guard Core.validInventory caseInventory

/-- Tamil COM/INST syncretism (-ōṭu covers both functions).
    Uses the cross-linguistic pattern from `Core.Case.Syncretism`. -/
def tamilComInstSync : Syncretism := comInstSyncretism

/-- COM/INST are strictly adjacent (ranks 1, 2). -/
theorem com_inst_adjacent :
    hierarchyAdjacent .com .inst = true := by native_decide

end Fragments.Tamil.Case
