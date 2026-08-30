import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Dimensions of measurement

The base dimensions a measure function measures in (mass, volume, distance, time,
cardinality, …) and the dimension group of the quantity calculus they generate: the free
abelian group on the base dimensions, written multiplicatively, so that
`.of .mass / .of .volume` is the dimension of density and `1` that of pure numbers.

## References

* [scontras-2014]
* [zabbal-2005]
* [de-boer-1995]
-/

namespace Degree

/-- A base dimension of measurement. `cardinality` is the dimension of [zabbal-2005]'s CARD,
the Num head behind cardinal numerals, aligned by [scontras-2014] with measure terms. -/
inductive Dimension where
  | mass
  | volume
  | distance
  | time
  | cardinality
  | temperature
  | area
  | force
  deriving Repr, DecidableEq, Fintype

/-- The dimensions of the quantity calculus: the free abelian group on the base
dimensions, written multiplicatively. -/
abbrev QuantityDimension := Multiplicative (Dimension → ℤ)

namespace QuantityDimension

/-- The base dimension `d` as a generator of the dimension group. -/
def of (d : Dimension) : QuantityDimension := .ofAdd (Pi.single d 1)

@[simp] theorem of_ne_one (d : Dimension) : of d ≠ 1 := by simp [of, Pi.single_eq_zero_iff]

theorem of_injective : Function.Injective of := λ d d' h => by
  simpa [of, Pi.single_apply, eq_comm] using congrFun (Multiplicative.ofAdd.injective h) d

@[simp] theorem of_inj {d d' : Dimension} : of d = of d' ↔ d = d' := of_injective.eq_iff

/-- Dividing by a base dimension changes the dimension. -/
@[simp] theorem div_of_ne_self (a : QuantityDimension) (d : Dimension) : a / of d ≠ a := λ h => by
  have := congrFun (congrArg Multiplicative.toAdd h) d
  simp [of] at this; omega

end QuantityDimension

end Degree
