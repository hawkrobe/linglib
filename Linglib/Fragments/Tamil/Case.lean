import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
import Linglib.Core.Case.Syncretism

/-!
# Tamil Case Inventory

Tamil (Dravidian) has **8 cases** with agglutinative suffixes:
NOM (∅), ACC (-ai), DAT (-ukku), GEN (-in / -uṭaiya), LOC (-il),
ABL (-ilirundu), INST / COM (-āl / -ōṭu), VOC (-ē).

The instrumental and comitative are sometimes syncretic (-ōṭu covers
both functions), a pattern documented cross-linguistically (Blake 1994;
WALS Ch. 52).

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press.
-/

namespace Fragments.Tamil.Case

/-- Tamil 7-case core inventory (excluding VOC). -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .abl, .inst, .com]

/-- Contiguous on Blake's hierarchy (ranks 6 down to 1). -/
theorem inventory_valid :
    Core.validInventory caseInventory = true := by native_decide

/-- Tamil COM/INST syncretism (-ōṭu). -/
def comInstSyncretism : Core.Syncretism :=
  ⟨.com, .inst, by decide⟩

/-- COM/INST are strictly adjacent (ranks 1, 2). -/
theorem com_inst_adjacent :
    Core.hierarchyAdjacent .com .inst = true := by native_decide

end Fragments.Tamil.Case
