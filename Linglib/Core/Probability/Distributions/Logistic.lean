/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Probability.CDF

/-!
# The logistic distribution

The standard logistic distribution is the probability measure on `ℝ` whose distribution function is
the sigmoid `σ x = 1 / (1 + exp (-x))`. It is the Stieltjes measure of `Real.sigmoid`, so its cdf is
the sigmoid (`cdf_logisticMeasure`) and its upper tail at `x` is `σ (-x)`
(`logisticMeasure_real_Ioi`), so the log-odds `Real.logit` invert the distribution function on
`(0, 1)`. `[UPSTREAM]` candidate for `Mathlib/Probability/Distributions/Logistic.lean`.

## Main definitions

* `ProbabilityTheory.logisticMeasure`: the standard logistic distribution.

## Main results

* `ProbabilityTheory.cdf_logisticMeasure`: the cdf of the standard logistic distribution is the
  sigmoid.
* `ProbabilityTheory.logisticMeasure_real_Ioi`: its upper tail at `x` is `σ (-x)`.
-/

@[expose] public section

open MeasureTheory Filter Set

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
