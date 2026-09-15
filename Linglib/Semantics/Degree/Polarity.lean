import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Scale polarity

This file defines `Degree.ScalePolarity`, which member of an antonym pair a gradable adjective
is. The two members measure on the same degrees under inverse orderings ([kennedy-2007] (60)
and fn. 29, [kennedy-mcnally-2005] fn. 7): the positive member (*tall*, *hot*) in the unmarked
direction, the negative member (*short*, *cold*) in the inverted one. Inverting an ordering
twice restores it, so polarities compose as the group of order two with `positive` as identity,
and `negative * p` is the polarity of the antonym of a `p` adjective. Its actions, on scale
boundedness and on the comparative, are in `Semantics/Degree/Boundedness` and
`Semantics/Degree/Basic`.

## Main definitions

* `ScalePolarity`, a `CommGroup` with `positive = 1`.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
-/

namespace Degree

/-- Which member of an antonym pair an adjective is: `positive` measures in the unmarked
direction (*tall*, *hot*), `negative` in the inverted one (*short*, *cold*). -/
inductive ScalePolarity where
  | positive
  | negative
  deriving DecidableEq, Repr, Fintype

namespace ScalePolarity

instance : One ScalePolarity := ⟨positive⟩

/-- Composition of orderings inversions: `negative * p` is the polarity of the antonym of a
`p` adjective. -/
instance : Mul ScalePolarity :=
  ⟨λ | positive, q => q | negative, positive => negative | negative, negative => positive⟩

@[simp] theorem positive_eq_one : positive = 1 := rfl

instance : CommGroup ScalePolarity where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv := id
  inv_mul_cancel := by decide
  mul_comm := by decide

@[simp] theorem negative_mul_negative : negative * negative = 1 := rfl

@[simp] theorem inv_eq (p : ScalePolarity) : p⁻¹ = p := rfl

@[simp] theorem mul_self (p : ScalePolarity) : p * p = 1 := by cases p <;> rfl

theorem eq_one_or_eq_negative (p : ScalePolarity) : p = 1 ∨ p = negative := by cases p <;> simp

theorem negative_ne_one : negative ≠ 1 := nofun

end ScalePolarity

end Degree
