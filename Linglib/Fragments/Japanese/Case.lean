import Linglib.Core.Case

/-!
# Japanese Case Inventory @cite{blake-1994}

Japanese marks case with postpositional particles:
- -ga (NOM), -o (ACC), -no (GEN), -ni (DAT/LOC/ALL)
- -kara (ABL), -de (INST/LOC), -to (COM), -e (ALL)

The particle -ni is highly polysemous, covering dative, locative, and
allative functions — a cross-linguistically common pattern that Blake
documents as ALL → DAT extension (Ch. 6). Similarly, -de covers both
instrumental and locative functions.

-/

namespace Fragments.Japanese.Case

/-- Japanese case inventory, mapped from particles to Core.Case:
    -ga → NOM, -o → ACC, -no → GEN, -ni → DAT/LOC/ALL,
    -kara → ABL, -de → INST (also LOC), -to → COM, -e → ALL. -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .abl, .all, .inst, .com]

-- Contiguous on Blake's hierarchy (ranks 6 down to 1, all present).
#guard Core.validInventory caseInventory

end Fragments.Japanese.Case
