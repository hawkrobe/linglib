import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

/-!
# Prototypes — Graded Category Membership

@cite{hudson-2010} Ch 2.

A prototype attaches a typicality grade (`ℚ`) to each member of a category.
Higher values are more prototypical. The structure is orthogonal to the
inheritance network in `Core.Inheritance.Basic`: it sits next to it, not
on top of it. Kept in its own file so consumers that only need the network
do not pay for `Mathlib.Data.Rat.Defs` and `Mathlib.Tactic.Linarith`.
-/

set_option autoImplicit false

namespace Core.Inheritance

/-- A prototype: a category with graded typicality over instances.
Higher values = more prototypical @cite{hudson-2010} Ch 2. -/
structure Prototype (α : Type) where
  category : α
  typicality : α → ℚ

/-- Whether `a` is at least as typical as `b` in a prototype. -/
def Prototype.atLeastAsTypical {α : Type} (proto : Prototype α) (a b : α) : Bool :=
  proto.typicality a ≥ proto.typicality b

/-- Whether `a` is strictly more typical than `b` in a prototype. -/
def Prototype.moreTypical {α : Type} (proto : Prototype α) (a b : α) : Bool :=
  proto.typicality a > proto.typicality b

/-- `atLeastAsTypical` is reflexive. -/
theorem Prototype.atLeastAsTypical_refl {α : Type} (proto : Prototype α) (a : α) :
    proto.atLeastAsTypical a a = true := by
  simp [atLeastAsTypical]

/-- `atLeastAsTypical` is transitive. -/
theorem Prototype.atLeastAsTypical_trans {α : Type} (proto : Prototype α) (a b c : α)
    (hab : proto.atLeastAsTypical a b = true)
    (hbc : proto.atLeastAsTypical b c = true) :
    proto.atLeastAsTypical a c = true := by
  simp [atLeastAsTypical] at *
  linarith

end Core.Inheritance
