/-
# Intensional Semantics Infrastructure

Core infrastructure for intensional semantics:
- World type (alias for Core.Proposition.World4)
- Intension type abbreviations
- Up/down operators for intension/extension conversion

For worked examples using this infrastructure, see:
- `Phenomena/Attitudes/IntensionalExamples.lean`

Reference: Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English.
-/

import Linglib.Theories.Semantics.Montague.Types
import Linglib.Core.Semantics.Proposition
import Linglib.Core.Semantics.Intension
-- Re-export modular attitude theories
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.Preferential

namespace Semantics.Attitudes.Intensional

open Semantics.Montague
open Core.Proposition (World4 FiniteWorlds)

/-- Canonical 4-world type for modal examples. Alias for `Core.Proposition.World4`. -/
abbrev World := World4

/-- List of all worlds. -/
def allWorlds : List World := FiniteWorlds.worlds

/-! ## Intension Types -/

/-- Shorthand for intension type (s ⇒ τ) -/
abbrev Ty.intens (τ : Ty) : Ty := .s ⇒ τ

/-- Proposition type: intension of truth values -/
abbrev Ty.prop : Ty := Ty.intens .t  -- s ⇒ t

/-- Individual concept: intension of entities -/
abbrev Ty.indConcept : Ty := Ty.intens .e  -- s ⇒ e

/-! ## Up/Down Operators -/

/-- The "up" operator (^): convert extension to intension (constant function).
In Montague's notation: ^α is the intension of α. -/
def up {m : Model} {τ : Ty} (x : m.interpTy τ) : m.interpTy (Ty.intens τ) :=
  λ _ => x

/-- The "down" operator (ˇ): evaluate intension at a world.
In Montague's notation: ˇα is the extension of α at the evaluation world. -/
def down {m : Model} {τ : Ty} (f : m.interpTy (Ty.intens τ)) (w : m.World) : m.interpTy τ :=
  f w

/-- The up operator equals Core.Intension.rigid. -/
theorem up_eq_rigid {m : Model} {τ : Ty} (x : m.interpTy τ) :
    up x = Core.Intension.rigid x := rfl

/-- The down operator equals Core.Intension.evalAt. -/
theorem down_eq_evalAt {m : Model} {τ : Ty} (f : m.interpTy (Ty.intens τ)) (w : m.World) :
    down f w = Core.Intension.evalAt f w := rfl

end Semantics.Attitudes.Intensional
