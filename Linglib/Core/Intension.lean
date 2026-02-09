/-
# Intensional Logic Primitives

Framework-agnostic types for intensional semantics: intensions as functions
from indices (possible worlds) to extensions, rigid designators, and evaluation.

These primitives are shared by `IntensionalSemantics/`, `TruthConditional/`,
and `RSA/` — any module that needs world-parameterized meanings.

## References

- Gallin (1975). Intensional and Higher-Order Modal Logic.
- von Fintel & Heim (2011). Intensional Semantics. Ch 1.
- SEP, "Intensional Logic".
-/

import Linglib.Core.Proposition

namespace Core.Intension

/-- An intension of type τ over indices W: a function from worlds to extensions. -/
abbrev Intension (W : Type*) (τ : Type*) := W → τ

/-- A rigid designator: an intension that returns the same value at every world. -/
def rigid {W τ : Type*} (x : τ) : Intension W τ := λ _ => x

/-- Evaluate an intension at a world to get its extension. -/
def evalAt {W τ : Type*} (f : Intension W τ) (w : W) : τ := f w

/-- An intension is rigid iff it assigns the same extension at every world. -/
def IsRigid {W τ : Type*} (f : Intension W τ) : Prop := ∀ w₁ w₂, f w₁ = f w₂

/-- A rigid designator is rigid. -/
theorem rigid_isRigid {W τ : Type*} (x : τ) : IsRigid (rigid (W := W) x) :=
  λ _ _ => rfl

/-- Propositions (W → Bool) are intensions of Bool, i.e. BProp. -/
theorem proposition_eq_bprop (W : Type*) : Intension W Bool = BProp W := rfl

/-- evalAt of rigid returns the original value. -/
theorem evalAt_rigid {W τ : Type*} (x : τ) (w : W) : evalAt (rigid x) w = x := rfl

/-- rigid is injective: different values give different intensions. -/
theorem rigid_injective {W τ : Type*} [Inhabited W] :
    Function.Injective (rigid (W := W) (τ := τ)) :=
  λ _ _ h => congr_fun h default

end Core.Intension
