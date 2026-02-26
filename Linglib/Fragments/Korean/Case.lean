import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy

/-!
# Korean Case Inventory

Korean marks case with postpositional particles:
- -i / -ga (NOM), -eul / -reul (ACC), -ui (GEN), -ege / -hante (DAT)
- -eseo (LOC), -buteo / -eseo (ABL), -(eu)ro (INST), -gwa / -wa (COM)

Like Japanese, Korean has a particle-based case system. The inventory
maps cleanly onto Blake's hierarchy with no gaps.

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press.
-/

namespace Fragments.Korean.Case

/-- Korean case inventory. -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .abl, .inst, .com]

/-- Contiguous on Blake's hierarchy (ranks 6 down to 1). -/
theorem inventory_valid :
    Core.validInventory caseInventory = true := by native_decide

end Fragments.Korean.Case
