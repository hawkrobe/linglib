/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Probability.CDF

/-!
# The logistic distribution

The standard logistic distribution is the probability measure on `ℝ` whose distribution function is
the sigmoid `σ x = 1 / (1 + exp (-x))`. It is the Stieltjes measure of `Real.sigmoid`, so its cdf is
the sigmoid (`cdf_logisticMeasure`) and its upper tail at `x` is `σ (-x)`
(`logisticMeasure_real_Ioi`). The odds of the sigmoid are exponential
(`Real.sigmoid_div_one_sub_sigmoid`), so the log-odds `p ↦ log (p / (1 - p))` invert the
distribution function on `(0, 1)`.
`[UPSTREAM]` candidates for `Mathlib/Probability/Distributions/Logistic.lean` and
`Mathlib/Analysis/SpecialFunctions/Sigmoid.lean`.

## Main definitions

* `ProbabilityTheory.logisticMeasure`: the standard logistic distribution.

## Main results

* `ProbabilityTheory.cdf_logisticMeasure`: the cdf of the standard logistic distribution is the
  sigmoid.
* `ProbabilityTheory.logisticMeasure_real_Ioi`: its upper tail at `x` is `σ (-x)`.
* `Real.log_sigmoid_div_one_sub_sigmoid`: the log-odds of `σ x` are `x`.
* `Real.sigmoid_log`: the sigmoid of the log-odds `log x` is `x / (x + 1)`.
-/

@[expose] public section

open MeasureTheory Filter Set

namespace Real

/-- The odds of the sigmoid are exponential. -/
theorem sigmoid_div_one_sub_sigmoid (x : ℝ) : sigmoid x / (1 - sigmoid x) = exp x := by
  rw [← sigmoid_neg, ← sigmoid_mul_rexp_neg, div_mul_cancel_left₀ (sigmoid_pos x).ne', exp_neg,
    inv_inv]

/-- The log-odds of the sigmoid are its argument. -/
theorem log_sigmoid_div_one_sub_sigmoid (x : ℝ) : log (sigmoid x / (1 - sigmoid x)) = x := by
  rw [sigmoid_div_one_sub_sigmoid, log_exp]

/-- The sigmoid of the logarithm of odds `x` is the probability `x / (x + 1)`. -/
theorem sigmoid_log {x : ℝ} (hx : 0 < x) : sigmoid (log x) = x / (x + 1) := by
  rw [sigmoid_def, exp_neg, exp_log hx]
  field_simp

end Real

namespace ProbabilityTheory

/-- The sigmoid as a Stieltjes function. -/
noncomputable def sigmoidStieltjes : StieltjesFunction ℝ where
  toFun := Real.sigmoid
  mono' := Real.sigmoid_monotone
  right_continuous' _ := continuous_sigmoid.continuousWithinAt

@[simp]
theorem sigmoidStieltjes_apply (x : ℝ) : sigmoidStieltjes x = Real.sigmoid x := rfl

/-- The standard logistic distribution, the probability measure whose distribution function is the
sigmoid. -/
noncomputable def logisticMeasure : Measure ℝ := sigmoidStieltjes.measure

instance : IsProbabilityMeasure logisticMeasure :=
  sigmoidStieltjes.isProbabilityMeasure Real.tendsto_sigmoid_atBot Real.tendsto_sigmoid_atTop

theorem cdf_logisticMeasure (x : ℝ) : cdf logisticMeasure x = Real.sigmoid x := by
  rw [logisticMeasure,
    cdf_measure_stieltjesFunction _ Real.tendsto_sigmoid_atBot Real.tendsto_sigmoid_atTop,
    sigmoidStieltjes_apply]

/-- The upper tail of the standard logistic distribution at `x` is the sigmoid at `-x`. -/
theorem logisticMeasure_real_Ioi (x : ℝ) : logisticMeasure.real (Ioi x) = Real.sigmoid (-x) := by
  rw [measureReal_def, logisticMeasure, sigmoidStieltjes.measure_Ioi Real.tendsto_sigmoid_atTop,
    sigmoidStieltjes_apply, ENNReal.toReal_ofReal (sub_nonneg.2 (Real.sigmoid_le_one x)),
    Real.sigmoid_neg]

end ProbabilityTheory
