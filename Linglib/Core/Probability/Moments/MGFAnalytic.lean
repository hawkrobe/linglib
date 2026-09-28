/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.MeanInequalities

/-!
# Convexity of the cumulant generating function  `[UPSTREAM]`

The cumulant generating function `cgf X μ` is convex on `integrableExpSet X μ`, the interval on
which the exponential moments are finite. Mathlib has its analyticity and first two derivatives
on the interior of that interval (`analyticOn_cgf`, `deriv_cgf`, `iteratedDeriv_two_cgf`), but
not its convexity on the whole interval.

Over a finite measure on a finite type, `cgf X μ` is a log-sum-exp, so this is the convexity of
the log-partition function of a log-linear model in its parameter.

## Main declarations

* `ProbabilityTheory.convexOn_cgf`: `cgf X μ` is convex on `integrableExpSet X μ`.

## Implementation notes

For `a + b = 1`, the weighted AM–GM inequality applied pointwise to `exp (s * X ω) / mgf X μ s`
and `exp (t * X ω) / mgf X μ t` and then integrated gives
`mgf X μ (a * s + b * t) ≤ mgf X μ s ^ a * mgf X μ t ^ b`, which is Hölder's inequality for the
exponential moments. Taking logarithms gives convexity.
-/

@[expose] public section

open MeasureTheory Real

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}

/-- The cumulant generating function is convex on the interval where it is finite. -/
theorem convexOn_cgf : ConvexOn ℝ (integrableExpSet X μ) (cgf X μ) := by
  refine ⟨convex_integrableExpSet, fun s hs t ht a b ha hb hab ↦ ?_⟩
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  have hst : a • s + b • t ∈ integrableExpSet X μ := convex_integrableExpSet hs ht ha hb hab
  simp only [smul_eq_mul] at hst ⊢
  have hA : 0 < mgf X μ s := mgf_pos' hμ hs
  have hB : 0 < mgf X μ t := mgf_pos' hμ ht
  have hAB : 0 < mgf X μ s ^ a * mgf X μ t ^ b :=
    mul_pos (rpow_pos_of_pos hA a) (rpow_pos_of_pos hB b)
  have hs' : Integrable (fun ω ↦ a * (exp (s * X ω) / mgf X μ s)) μ := (hs.div_const _).const_mul a
  have ht' : Integrable (fun ω ↦ b * (exp (t * X ω) / mgf X μ t)) μ := (ht.div_const _).const_mul b
  have hpt : (fun ω ↦ exp ((a * s + b * t) * X ω)) ≤ fun ω ↦
      mgf X μ s ^ a * mgf X μ t ^ b *
        (a * (exp (s * X ω) / mgf X μ s) + b * (exp (t * X ω) / mgf X μ t)) := fun ω ↦ by
    have h := geom_mean_le_arith_mean2_weighted ha hb (div_pos (exp_pos (s * X ω)) hA).le
      (div_pos (exp_pos (t * X ω)) hB).le hab
    rw [div_rpow (exp_pos _).le hA.le, div_rpow (exp_pos _).le hB.le, ← exp_mul, ← exp_mul] at h
    calc exp ((a * s + b * t) * X ω)
        = mgf X μ s ^ a * mgf X μ t ^ b *
            (exp (s * X ω * a) / mgf X μ s ^ a * (exp (t * X ω * b) / mgf X μ t ^ b)) := by
          field_simp
          rw [← exp_add]
          ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left h hAB.le
  have hle : mgf X μ (a * s + b * t) ≤ mgf X μ s ^ a * mgf X μ t ^ b :=
    calc mgf X μ (a * s + b * t)
        ≤ ∫ ω, mgf X μ s ^ a * mgf X μ t ^ b *
            (a * (exp (s * X ω) / mgf X μ s) + b * (exp (t * X ω) / mgf X μ t)) ∂μ :=
          integral_mono hst ((hs'.add ht').const_mul _) hpt
      _ = mgf X μ s ^ a * mgf X μ t ^ b := by
          rw [integral_const_mul, integral_add hs' ht', integral_const_mul, integral_const_mul,
            integral_div, integral_div]
          change _ * (a * (mgf X μ s / mgf X μ s) + b * (mgf X μ t / mgf X μ t)) = _
          rw [div_self hA.ne', div_self hB.ne', mul_one, mul_one, hab, mul_one]
  calc cgf X μ (a * s + b * t) = log (mgf X μ (a * s + b * t)) := rfl
    _ ≤ log (mgf X μ s ^ a * mgf X μ t ^ b) := log_le_log (mgf_pos' hμ hst) hle
    _ = a * cgf X μ s + b * cgf X μ t := by
      rw [log_mul (rpow_pos_of_pos hA a).ne' (rpow_pos_of_pos hB b).ne', log_rpow hA, log_rpow hB]
      rfl

end ProbabilityTheory
