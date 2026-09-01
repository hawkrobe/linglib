/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Moments.Variance

/-!
# Bernoulli distribution: bind and variance

Binding a kernel through `Ber(x, y, p)` is the `p`-mixture of its two values, and the variance of
a real observable under `Ber(x, y, p)` is `p * (1 - p) * (f x - f y) ^ 2`.

## Main results

* `ProbabilityTheory.bernoulliMeasure_bind`: `Ber(x, y, p).bind f = p • f x + (1 - p) • f y`.
* `ProbabilityTheory.variance_bernoulliMeasure`:
  `Var[f; Ber(x, y, p)] = p * (1 - p) * (f x - f y) ^ 2`.

[UPSTREAM] candidates for `Mathlib.Probability.Distributions.Bernoulli`.
-/

open MeasureTheory unitInterval

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass X]
  (x y : X) (p : I)

theorem bernoulliMeasure_bind {f : X → Measure Y} (hf : Measurable f) :
    Ber(x, y, p).bind f = toNNReal p • f x + toNNReal (σ p) • f y := by
  ext s hs
  simp [bernoulliMeasure_def, Measure.bind_apply hs hf.aemeasurable, lintegral_add_measure,
    lintegral_smul_measure]

theorem variance_bernoulliMeasure {f : X → ℝ} (hf : AEMeasurable f Ber(x, y, p)) :
    Var[f; Ber(x, y, p)] = p * (1 - p) * (f x - f y) ^ 2 := by
  rw [variance_eq_integral hf]
  simp only [integral_bernoulliMeasure, smul_eq_mul]
  ring

end ProbabilityTheory
