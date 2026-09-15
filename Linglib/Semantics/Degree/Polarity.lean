import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Group.Action.Defs

/-!
# Polarity

This file defines `Degree.Polarity`, which member of an antonym pair a gradable adjective is.
The two members measure on the same degrees under inverse orderings ([kennedy-2007] (60) and
fn. 29, [kennedy-mcnally-2005] fn. 7): the positive member (*tall*, *hot*) in the unmarked
direction, the negative member (*short*, *cold*) in the inverted one. Inverting an ordering
twice restores it, so polarities compose as the sign group `ℤˣ`, `positive` being `1` and
`negative` being `-1`, and `negative * p` is the polarity of the antonym of a `p` adjective. The
sign acts on scale boundedness through the order dual (`Semantics/Degree/Boundedness`) and on
an additive scale by negating the measure (`Semantics/Degree/Basic`).

## Main definitions

* `Polarity`, the sign group `ℤˣ`, with its two members `Polarity.positive` and
  `Polarity.negative`.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
-/

namespace Degree

/-- Which member of an antonym pair an adjective is, as a sign: `positive` measures in the
unmarked direction (*tall*, *hot*), `negative` in the inverted one (*short*, *cold*). -/
abbrev Polarity := ℤˣ

namespace Polarity

/-- The unmarked member of an antonym pair (*tall*, *hot*). -/
def positive : Polarity := 1

/-- The marked member of an antonym pair (*short*, *cold*). -/
def negative : Polarity := -1

theorem positive_eq_one : positive = 1 := rfl

theorem negative_eq_neg_one : negative = -1 := rfl

@[simp] theorem negative_ne_positive : negative ≠ positive := by decide

@[simp] theorem positive_ne_negative : positive ≠ negative := by decide

theorem eq_positive_or_eq_negative (p : Polarity) : p = positive ∨ p = negative :=
  Int.units_eq_one_or p

@[simp] theorem positive_mul (p : Polarity) : positive * p = p := one_mul p

@[simp] theorem mul_positive (p : Polarity) : p * positive = p := mul_one p

/-- Two inversions restore the ordering: the antonym of *short* is *tall*, and *less short than*
is *taller than*. Sentential negation is not a polarity: *not short* is the contradictory of
*short* and does not entail *tall* (`Degree.Antonymy`). -/
@[simp] theorem negative_mul_negative : negative * negative = positive := by decide

@[simp] theorem mul_self (p : Polarity) : p * p = positive := by
  rcases eq_positive_or_eq_negative p with rfl | rfl <;> decide

@[simp] theorem inv_eq_self (p : Polarity) : p⁻¹ = p := by
  rcases eq_positive_or_eq_negative p with rfl | rfl <;> decide

@[simp] theorem positive_smul {M : Type*} [MulAction Polarity M] (x : M) : positive • x = x :=
  one_smul _ x

end Polarity

end Degree
