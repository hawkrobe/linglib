/-
# Intensional Semantics Infrastructure

Core infrastructure for intensional semantics:
- World type (a 4-world example)
- Intension type abbreviations (now in Core.IntensionalLogic.Frame)
- Up/down operators (now in Core.IntensionalLogic.Frame)

For worked examples using this infrastructure, see:
- `Phenomena/Attitudes/Studies/Montague1973.lean`
-/

import Linglib.Core.IntensionalLogic.Frame
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Linglib.Core.IntensionalLogic.Rigidity
-- Re-export modular attitude theories
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.Preferential

namespace Semantics.Attitudes.Intensional

open Core.IntensionalLogic

/-- Canonical 4-world type for modal examples. -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr, Inhabited

instance : Fintype World where
  elems := {.w0, .w1, .w2, .w3}
  complete := λ w => by cases w <;> simp

/-- List of all worlds. -/
def allWorlds : List World := [.w0, .w1, .w2, .w3]

theorem mem_allWorlds (w : World) : w ∈ allWorlds := by
  cases w <;> simp [allWorlds]

/-! ## Up/Down Operators

The `up` and `down` operators are defined in `Core.IntensionalLogic.Frame`.
Use `up`/`down` from `Core.IntensionalLogic` directly.

The `Ty.intens`, `Ty.prop`, and `Ty.indConcept` abbreviations are also
in `Core.IntensionalLogic.Frame`. -/

end Semantics.Attitudes.Intensional
