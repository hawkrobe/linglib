/-
# Intensional Semantics Infrastructure

Core infrastructure for intensional semantics:
- World type (alias for Core.Proposition.World4)
- Intension type abbreviations
- IModel structure for intensional models
- Up/down operators for intension/extension conversion

For worked examples using this infrastructure, see:
- `Phenomena/Attitudes/IntensionalExamples.lean`

Reference: Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English.
-/

import Linglib.Theories.Semantics.Compositional.Basic
import Linglib.Core.Proposition
import Linglib.Core.Intension
-- Re-export modular attitude theories
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.Preferential

namespace Semantics.Attitudes.Intensional

open Semantics.Compositional
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

/-! ## Intensional Models -/

/-- An intensional model specifies an entity domain. -/
structure IModel where
  /-- The domain of entities -/
  Entity : Type
  /-- Decidable equality on entities -/
  decEq : DecidableEq Entity

/-- Interpretation of types in an intensional model -/
def IModel.interpTy (m : IModel) : Ty → Type
  | .e => m.Entity
  | .t => Bool
  | .s => World
  | .fn σ τ => m.interpTy σ → m.interpTy τ

/-! ## Up/Down Operators -/

/-- The "up" operator (^): convert extension to intension (constant function).
In Montague's notation: ^α is the intension of α. -/
def up {m : IModel} {τ : Ty} (x : m.interpTy τ) : m.interpTy (Ty.intens τ) :=
  λ _ => x

/-- The "down" operator (ˇ): evaluate intension at a world.
In Montague's notation: ˇα is the extension of α at the evaluation world. -/
def down {m : IModel} {τ : Ty} (f : m.interpTy (Ty.intens τ)) (w : World) : m.interpTy τ :=
  f w

/-- The up operator equals Core.Intension.rigid. -/
theorem up_eq_rigid {m : IModel} {τ : Ty} (x : m.interpTy τ) :
    up x = Core.Intension.rigid x := rfl

/-- The down operator equals Core.Intension.evalAt. -/
theorem down_eq_evalAt {m : IModel} {τ : Ty} (f : m.interpTy (Ty.intens τ)) (w : World) :
    down f w = Core.Intension.evalAt f w := rfl

end Semantics.Attitudes.Intensional
