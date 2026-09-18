/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monovary
import Mathlib.Tactic.Module

/-!
# Weighted Chebyshev sum inequality  `[UPSTREAM]`

Mathlib's Chebyshev sum inequality (`MonovaryOn.sum_smul_sum_le_card_smul_sum`) counts every
index once. This file weights the indices: for nonnegative weights `w` and functions `f` and `g`
that monovary,
`(∑ i ∈ s, w i * f i) • ∑ i ∈ s, w i • g i ≤ (∑ i ∈ s, w i) • ∑ i ∈ s, (w i * f i) • g i`,
and the reverse inequality when `f` and `g` antivary. With the weights a probability
distribution this is the covariance inequality `E[f] E[g] ≤ E[f g]` for similarly ordered `f`
and `g`.

## Main declarations

* `MonovaryOn.sum_mul_smul_sum_smul_le_sum_smul_sum_mul_smul`: the weighted Chebyshev
  inequality.
* `AntivaryOn.sum_smul_sum_mul_smul_le_sum_mul_smul_sum_smul`: the weighted Chebyshev
  inequality, dual version.
* `MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul`,
  `AntivaryOn.sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul`: the multiplication versions.
* `two_nsmul_sum_smul_sum_smul_sub`: twice the weighted covariance defect is the double sum of
  the weighted products of pairwise differences, the identity behind the inequality.

## Implementation notes

As in `Mathlib/Algebra/Order/Chebyshev.lean`, multiplication is decoupled into scalar
multiplication with `f` and `g` landing in different types, so that the antivarying statement
is the monovarying one on the order dual. Unlike the unweighted inequality, which mathlib
derives from the rearrangement inequality by cycling the indices, the weighted one is derived
from the double-sum identity, which needs subtraction and weights that commute with `f`; hence
`CommRing` and `AddCommGroup` in place of mathlib's `Semiring` and `AddCommMonoid`.
-/

open Finset

variable {ι α β : Type*}

/-! ### Scalar multiplication versions -/

section SMul

variable [CommRing α] [AddCommGroup β] [Module α β] (w f : ι → α) (g : ι → β) (s : Finset ι)

/-- Twice the covariance defect of weighted sums is the weighted double sum of the products of
pairwise differences. -/
theorem two_nsmul_sum_smul_sum_smul_sub :
    2 • ((∑ i ∈ s, w i) • ∑ i ∈ s, (w i * f i) • g i -
        (∑ i ∈ s, w i * f i) • ∑ i ∈ s, w i • g i) =
      ∑ i ∈ s, ∑ j ∈ s, (w i * w j) • ((f i - f j) • (g i - g j)) := by
  have h (i : ι) : ∑ j ∈ s, (w i * w j) • ((f i - f j) • (g i - g j)) =
      (∑ j ∈ s, w j) • ((w i * f i) • g i) - (w i * f i) • ∑ j ∈ s, w j • g j -
        (∑ j ∈ s, w j * f j) • (w i • g i) + w i • ∑ j ∈ s, (w j * f j) • g j := by
    simp only [smul_sum, sum_smul, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun j _ ↦ by module
  simp only [h, sum_add_distrib, sum_sub_distrib, ← smul_sum, ← sum_smul]
  module

variable {w f g s} [LinearOrder α] [IsStrictOrderedRing α] [LinearOrder β]
  [IsOrderedAddMonoid β] [IsStrictOrderedModule α β]

/-- **Weighted Chebyshev sum inequality**: when `f` and `g` monovary together, the scalar
product of their `w`-weighted sums is at most the total weight times their `w`-weighted scalar
product, for nonnegative weights `w`. -/
theorem MonovaryOn.sum_mul_smul_sum_smul_le_sum_smul_sum_mul_smul (hfg : MonovaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) • ∑ i ∈ s, w i • g i ≤ (∑ i ∈ s, w i) • ∑ i ∈ s, (w i * f i) • g i := by
  rw [← sub_nonneg, ← nsmul_nonneg_iff two_ne_zero, two_nsmul_sum_smul_sum_smul_sub]
  exact sum_nonneg fun i hi ↦ sum_nonneg fun j hj ↦
    smul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hfg.sub_smul_sub_nonneg hj hi)

/-- **Weighted Chebyshev sum inequality**: when `f` and `g` antivary together, the scalar
product of their `w`-weighted sums is at least the total weight times their `w`-weighted scalar
product, for nonnegative weights `w`. -/
theorem AntivaryOn.sum_smul_sum_mul_smul_le_sum_mul_smul_sum_smul (hfg : AntivaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) • ∑ i ∈ s, (w i * f i) • g i ≤ (∑ i ∈ s, w i * f i) • ∑ i ∈ s, w i • g i :=
  hfg.dual_right.sum_mul_smul_sum_smul_le_sum_smul_sum_mul_smul hw

variable [Fintype ι]

/-- **Weighted Chebyshev sum inequality**, over a finite type. -/
theorem Monovary.sum_mul_smul_sum_smul_le_sum_smul_sum_mul_smul (hfg : Monovary f g)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i) • ∑ i, w i • g i ≤ (∑ i, w i) • ∑ i, (w i * f i) • g i :=
  (hfg.monovaryOn _).sum_mul_smul_sum_smul_le_sum_smul_sum_mul_smul fun i _ ↦ hw i

/-- **Weighted Chebyshev sum inequality**, dual version over a finite type. -/
theorem Antivary.sum_smul_sum_mul_smul_le_sum_mul_smul_sum_smul (hfg : Antivary f g)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i) • ∑ i, (w i * f i) • g i ≤ (∑ i, w i * f i) • ∑ i, w i • g i :=
  (hfg.antivaryOn _).sum_smul_sum_mul_smul_le_sum_mul_smul_sum_smul fun i _ ↦ hw i

end SMul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/

section Mul

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] {w f g : ι → α} {s : Finset ι}

/-- **Weighted Chebyshev sum inequality**: when `f` and `g` monovary together, the product of
their `w`-weighted sums is at most the total weight times their `w`-weighted product, for
nonnegative weights `w`. -/
theorem MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul (hfg : MonovaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i := by
  simpa only [smul_eq_mul] using hfg.sum_mul_smul_sum_smul_le_sum_smul_sum_mul_smul hw

/-- **Weighted Chebyshev sum inequality**: when `f` and `g` antivary together, the product of
their `w`-weighted sums is at least the total weight times their `w`-weighted product, for
nonnegative weights `w`. -/
theorem AntivaryOn.sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul (hfg : AntivaryOn f g s)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i * g i ≤ (∑ i ∈ s, w i * f i) * ∑ i ∈ s, w i * g i := by
  simpa only [smul_eq_mul] using hfg.sum_smul_sum_mul_smul_le_sum_mul_smul_sum_smul hw

variable [Fintype ι]

/-- **Weighted Chebyshev sum inequality**, over a finite type. -/
theorem Monovary.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul (hfg : Monovary f g)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i) * ∑ i, w i * g i ≤ (∑ i, w i) * ∑ i, w i * f i * g i :=
  (hfg.monovaryOn _).sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul fun i _ ↦ hw i

/-- **Weighted Chebyshev sum inequality**, dual version over a finite type. -/
theorem Antivary.sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul (hfg : Antivary f g)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i) * ∑ i, w i * f i * g i ≤ (∑ i, w i * f i) * ∑ i, w i * g i :=
  (hfg.antivaryOn _).sum_mul_sum_mul_mul_le_sum_mul_mul_sum_mul fun i _ ↦ hw i

end Mul
