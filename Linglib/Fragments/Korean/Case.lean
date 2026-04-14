import Linglib.Core.Case

/-!
# Korean Case Inventory
@cite{blake-1994}

Korean marks case with postpositional particles:
- -i / -ga (NOM), -eul / -reul (ACC), -ui (GEN), -ege / -hante (DAT)
- -eseo (LOC), -buteo / -eseo (ABL), -(eu)ro (INST), -gwa / -wa (COM)

Like Japanese, Korean has a particle-based case system. The inventory
maps cleanly onto Blake's hierarchy with no gaps.

-/

namespace Fragments.Korean.Case

/-- Korean case inventory. -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .abl, .inst, .com]

-- Contiguous on Blake's hierarchy (ranks 6 down to 1).
#guard Core.validInventory caseInventory

end Fragments.Korean.Case
