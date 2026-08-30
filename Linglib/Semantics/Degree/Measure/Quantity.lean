import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Linglib.Semantics.Degree.Measure.Dimensioned

/-!
# The quantity calculus

A quantity is a magnitude together with a dimension: `0.9 g` is a magnitude in the
dimension of mass, `0.9 g/mL` one in the dimension of density, and `9` is a pure number,
a magnitude in the identity dimension. This file sets up the quantity calculus that
measure-phrase semantics computes in. Dimensions form the free abelian group on the base
`Dimension`s, written multiplicatively, so that `.of .mass / .of .volume` is the dimension
of density; quantities are pairs `K × QuantityDimension` of a magnitude and a dimension and
multiply and divide componentwise, so that dividing two quantities of one dimension yields a
pure number.

## Main definitions

* `QuantityDimension`, `QuantityDimension.of`: the dimension group and its generators.
* `Quantity`, `Quantity.pure`, `Quantity.unit`: quantities, pure numbers, unit quantities.
* `DimensionedMeasure.quantity`: the value of a measure function as a quantity.

## References

* [de-boer-1995]
* [coppock-2021]
-/

namespace Degree

open Features (Dimension)

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
@[simp] theorem div_of_ne_self (a : QuantityDimension) (d : Dimension) : a / of d ≠ a := by
  simp [div_eq_self]

end QuantityDimension

/-- A quantity, a magnitude in `K` with a dimension. Quantities multiply and divide
componentwise. -/
abbrev Quantity (K : Type*) := K × QuantityDimension

namespace Quantity

variable {K : Type*}

/-- The pure number `n`, a quantity `(n, 1)` of the identity dimension. -/
def pure (n : K) : Quantity K := (n, 1)

/-- The unit quantity `(1, d)` of the base dimension `d`. -/
def unit [One K] (d : Dimension) : Quantity K := (1, .of d)

@[simp] theorem pure_fst (n : K) : (pure n).1 = n := rfl
@[simp] theorem pure_snd (n : K) : (pure n).2 = 1 := rfl
@[simp] theorem unit_fst [One K] (d : Dimension) : (unit d : Quantity K).1 = 1 := rfl
@[simp] theorem unit_snd [One K] (d : Dimension) : (unit d : Quantity K).2 = .of d := rfl

variable [CommGroupWithZero K]

/-- Scaling both quantities by the same nonzero pure number leaves their quotient
unchanged: `0.1 kg / L = 0.1 g / mL`. -/
theorem pure_mul_div_pure_mul {k : K} (hk : k ≠ 0) (q r : Quantity K) :
    pure k * q / (pure k * r) = q / r := by
  ext <;> simp [mul_div_mul_left _ _ hk]

/-- `a / b = q / r ↔ a = q * (b / r)` when the magnitudes of `b` and `r` are nonzero. -/
theorem div_eq_div_iff_eq_mul_div {a b q r : Quantity K} (hb : b.1 ≠ 0) (hr : r.1 ≠ 0) :
    a / b = q / r ↔ a = q * (b / r) := by
  rw [Prod.ext_iff, Prod.ext_iff]
  simp only [Prod.fst_div, Prod.snd_div, Prod.fst_mul, Prod.snd_mul, ← mul_div_assoc]
  rw [div_eq_div_iff hb hr, eq_div_iff hr, div_eq_div_iff_mul_eq_mul, eq_div_iff_mul_eq']

/-- The quotient of two quantities of one dimension is the pure number `n` with `n ⋅ q = a`. -/
theorem div_eq_pure_iff {a q : Quantity K} {n : K} (hq : q.1 ≠ 0) (h : a.2 = q.2) :
    a / q = pure n ↔ pure n * q = a := by
  simp only [Prod.ext_iff, Prod.fst_div, Prod.snd_div, Prod.fst_mul, Prod.snd_mul, pure_fst,
    pure_snd, h, div_self', one_mul, and_true, div_eq_iff hq]
  exact eq_comm

end Quantity

variable {E : Type*} {K : Type}

/-- The value of `μ` at `x` as a quantity of `μ`'s dimension. -/
def DimensionedMeasure.quantity (μ : DimensionedMeasure E K) (x : E) : Quantity K :=
  (μ x, .of μ.dimension)

@[simp] theorem DimensionedMeasure.quantity_fst (μ : DimensionedMeasure E K) (x : E) :
    (μ.quantity x).1 = μ x := rfl

@[simp] theorem DimensionedMeasure.quantity_snd (μ : DimensionedMeasure E K) (x : E) :
    (μ.quantity x).2 = .of μ.dimension := rfl

/-- Measuring `n` units is having the quantity `n` times the unit. -/
theorem DimensionedMeasure.quantity_eq_pure_mul_unit_iff [MulOneClass K] [Preorder K]
    (μ : DimensionedMeasure E K) (n : K) (x : E) :
    μ.quantity x = .pure n * .unit μ.dimension ↔ μ.applyNumeral n x := by
  simp [Prod.ext_iff]

end Degree
