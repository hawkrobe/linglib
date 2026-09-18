/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Order.Monovary
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Covariance

/-!
# Chebyshev's integral inequality  `[UPSTREAM]`

Two real random variables that monovary have nonnegative covariance, and two that antivary
have nonpositive covariance. On a finite measure the statement is
`(∫ X ∂μ) * ∫ Y ∂μ ≤ μ.real univ * ∫ X * Y ∂μ`, the integral form of Chebyshev's sum
inequality (`MonovaryOn.sum_mul_sum_le_card_mul_sum`); on a probability measure it reads
`0 ≤ cov[X, Y; μ]`.

## Main declarations

* `Monovary.integral_mul_integral_le_measureReal_univ_mul_integral`,
  `Antivary.measureReal_univ_mul_integral_le_integral_mul_integral`: Chebyshev's integral
  inequality on a finite measure and its dual.
* `Monovary.covariance_nonneg`, `Antivary.covariance_nonpos`: the covariance forms.

## Implementation notes

The proof integrates `0 ≤ (X ω - X ω') * (Y ω - Y ω')`, pointwise nonnegative by
`Monovary.sub_mul_sub_nonneg`, over the product measure `μ.prod μ`, where it expands to twice
the covariance defect. The dual follows by negating `X`.
-/

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → ℝ}

section FiniteMeasure

variable [IsFiniteMeasure μ] (hX : Integrable X μ) (hY : Integrable Y μ)
  (hXY : Integrable (X * Y) μ)
include hX hY hXY

/-- **Chebyshev's integral inequality**: when `X` and `Y` monovary, the product of their
integrals is at most the total mass times the integral of their product. -/
theorem Monovary.integral_mul_integral_le_measureReal_univ_mul_integral (h : Monovary X Y) :
    (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ ≤ μ.real Set.univ * ∫ ω, X ω * Y ω ∂μ := by
  have h₁ := hXY.mul_prod (μ := μ) (ν := μ) (integrable_const (1 : ℝ))
  have h₂ := hX.mul_prod (μ := μ) (ν := μ) hY
  have h₃ := hY.mul_prod (μ := μ) (ν := μ) hX
  have h₄ := (integrable_const (1 : ℝ)).mul_prod (μ := μ) (ν := μ) hXY
  have key : ∫ z, (X z.1 - X z.2) * (Y z.1 - Y z.2) ∂(μ.prod μ) =
      2 * (μ.real Set.univ * ∫ ω, X ω * Y ω ∂μ - (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ) := by
    have e : (fun z : Ω × Ω ↦ (X z.1 - X z.2) * (Y z.1 - Y z.2)) = fun z ↦
        ((X * Y) z.1 * (1 : Ω → ℝ) z.2 - X z.1 * Y z.2) -
          (Y z.1 * X z.2 - (1 : Ω → ℝ) z.1 * (X * Y) z.2) := by
      ext z; simp only [Pi.mul_apply, Pi.one_apply]; ring
    rw [e, integral_sub, integral_sub, integral_sub, integral_prod_mul, integral_prod_mul,
      integral_prod_mul, integral_prod_mul]
    · simp only [Pi.mul_apply, Pi.one_apply, integral_const, smul_eq_mul, mul_one]; ring
    all_goals first | exact h₁ | exact h₂ | exact h₃ | exact h₄ | exact h₁.sub h₂ | exact h₃.sub h₄
  have h₀ : 0 ≤ ∫ z, (X z.1 - X z.2) * (Y z.1 - Y z.2) ∂(μ.prod μ) :=
    integral_nonneg fun z ↦ h.sub_mul_sub_nonneg z.2 z.1
  linarith

/-- **Chebyshev's integral inequality**: when `X` and `Y` antivary, the product of their
integrals is at least the total mass times the integral of their product. -/
theorem Antivary.measureReal_univ_mul_integral_le_integral_mul_integral (h : Antivary X Y) :
    μ.real Set.univ * ∫ ω, X ω * Y ω ∂μ ≤ (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ := by
  have := (monovary_neg_left.2 h).integral_mul_integral_le_measureReal_univ_mul_integral
    hX.neg hY (by simpa only [neg_mul] using hXY.neg)
  simpa only [Pi.neg_apply, neg_mul, integral_neg, mul_neg, neg_le_neg_iff] using this

end FiniteMeasure

section ProbabilityMeasure

open ProbabilityTheory

variable [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
include hX hY

/-- Random variables that monovary have nonnegative covariance. -/
theorem Monovary.covariance_nonneg (h : Monovary X Y) : 0 ≤ cov[X, Y; μ] := by
  rw [covariance_eq_sub hX hY, sub_nonneg]
  simpa [probReal_univ] using h.integral_mul_integral_le_measureReal_univ_mul_integral
    (hX.integrable one_le_two) (hY.integrable one_le_two) (hX.integrable_mul hY)

/-- Random variables that antivary have nonpositive covariance. -/
theorem Antivary.covariance_nonpos (h : Antivary X Y) : cov[X, Y; μ] ≤ 0 := by
  rw [covariance_eq_sub hX hY, sub_nonpos]
  simpa [probReal_univ] using h.measureReal_univ_mul_integral_le_integral_mul_integral
    (hX.integrable one_le_two) (hY.integrable one_le_two) (hX.integrable_mul hY)

end ProbabilityMeasure
