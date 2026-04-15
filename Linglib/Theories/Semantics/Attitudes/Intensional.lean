/-
# Intensional Semantics Infrastructure

Core infrastructure for intensional semantics:
- World type (alias for Core.Proposition.World4)
- Intension type abbreviations (now in Core.IntensionalLogic.Frame)
- Up/down operators (now in Core.IntensionalLogic.Frame)

For worked examples using this infrastructure, see:
- `Phenomena/Attitudes/IntensionalExamples.lean`
-/

import Linglib.Core.IntensionalLogic.Frame
import Linglib.Core.Semantics.Proposition
import Linglib.Core.IntensionalLogic.Rigidity
-- Re-export modular attitude theories
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.Preferential

namespace Semantics.Attitudes.Intensional

open Core.IntensionalLogic
open Core.Proposition (World4 FiniteWorlds)

/-- Canonical 4-world type for modal examples. Alias for `Core.Proposition.World4`. -/
abbrev World := World4

/-- List of all worlds. -/
def allWorlds : List World := FiniteWorlds.worlds

/-! ## Up/Down Operators

The `up` and `down` operators are defined in `Core.IntensionalLogic.Frame`.
Use `up`/`down` from `Core.IntensionalLogic` directly.

The `Ty.intens`, `Ty.prop`, and `Ty.indConcept` abbreviations are also
in `Core.IntensionalLogic.Frame`. -/

end Semantics.Attitudes.Intensional
