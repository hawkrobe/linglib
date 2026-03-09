import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

/-!
# Standard Normal CDF Infrastructure
@cite{luce-1959}

Shared Gaussian CDF definitions and properties used by both Thurstone's
discriminal-process theory (§2.D) and Signal Detection Theory (§2.E)
in @cite{luce-1959}.

## Definitions

- `normalPDF`: the standard normal density φ(t) = (1/√(2π)) exp(−t²/2)
- `normalCDF`: the standard normal CDF Φ(x) = ∫_{−∞}^{x} φ(t) dt

## Properties

Monotonicity, strict monotonicity, symmetry, boundary values, and bounds.
The CDF is defined via Mathlib's `cdf (gaussianReal 0 1)`, which gives
`normalCDF x = (gaussianReal 0 1).real (Iic x)`. This grounds the properties
in Mathlib's measure-theoretic Gaussian infrastructure.
-/

set_option autoImplicit false

namespace Core

open Real MeasureTheory BigOperators Set ProbabilityTheory NNReal

-- ============================================================================
-- §1. Normal PDF
-- ============================================================================

/-- The standard normal probability density function: `φ(t) = (1/√(2π)) · exp(-t²/2)`. -/
noncomputable def normalPDF (t : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2)

-- ============================================================================
-- §2. Normal CDF
-- ============================================================================

/-- The standard normal cumulative distribution function:
    `Φ(x) = ∫_{-∞}^{x} (1/√(2π)) exp(-t²/2) dt`.

    Defined as `cdf (gaussianReal 0 1) x`, the CDF of the standard Gaussian
    measure evaluated at `x`. -/
noncomputable def normalCDF (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

-- ============================================================================
-- §3. Helper lemmas for the standard Gaussian
-- ============================================================================

private noncomputable abbrev stdGaussian : Measure ℝ := gaussianReal (0 : ℝ) (1 : ℝ≥0)

private theorem std_var_ne_zero : (1 : ℝ≥0) ≠ 0 := by positivity

private theorem stdGaussian_unfold :
    stdGaussian = volume.withDensity (gaussianPDF 0 1) :=
  gaussianReal_of_var_ne_zero 0 std_var_ne_zero

private theorem stdGaussian_ac : stdGaussian.AbsolutelyContinuous volume := by
  rw [stdGaussian_unfold]
  exact withDensity_absolutelyContinuous _ _

private theorem stdGaussian_singleton (x : ℝ) : stdGaussian {x} = 0 :=
  stdGaussian_ac (measure_singleton x)

private theorem stdGaussian_symm :
    Measure.map (fun x : ℝ => -x) stdGaussian = stdGaussian := by
  show Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) = gaussianReal 0 1
  have h := @gaussianReal_map_neg (0 : ℝ) (1 : ℝ≥0)
  simp only [neg_zero] at h; exact h

-- ============================================================================
-- §4. Properties
-- ============================================================================

/-- The normal CDF is non-negative: `Φ(x) ≥ 0` for all `x`. -/
theorem normalCDF_nonneg (x : ℝ) : 0 ≤ normalCDF x := cdf_nonneg _ x

/-- The normal CDF is at most 1: `Φ(x) ≤ 1` for all `x`. -/
theorem normalCDF_le_one (x : ℝ) : normalCDF x ≤ 1 := cdf_le_one _ x

/-- The normal CDF is monotone increasing. -/
theorem normalCDF_mono : Monotone normalCDF := monotone_cdf _

/-- Symmetry: `Φ(-x) = 1 - Φ(x)`. -/
theorem normalCDF_neg (x : ℝ) : normalCDF (-x) = 1 - normalCDF x := by
  simp only [normalCDF, cdf_eq_real]
  have h_sym : stdGaussian (Ici (-x)) = stdGaussian (Iic x) := by
    conv_lhs => rw [← stdGaussian_symm]
    rw [Measure.map_apply measurable_neg measurableSet_Ici]
    congr 1; ext t; simp [mem_Iic]
  have h_Ici_Ioi : stdGaussian (Ici (-x)) = stdGaussian (Ioi (-x)) := by
    have hsplit : Ici (-x) = {-x} ∪ Ioi (-x) := by ext t; simp [le_iff_lt_or_eq, or_comm]
    rw [hsplit, measure_union _ measurableSet_Ioi, stdGaussian_singleton, zero_add]
    exact Set.disjoint_left.mpr fun t ht1 ht2 =>
      lt_irrefl _ (mem_singleton_iff.mp ht1 ▸ mem_Ioi.mp ht2)
  have h_compl : stdGaussian.real (Iic (-x)) + stdGaussian.real (Ioi (-x)) = 1 := by
    have hunion : stdGaussian.real (Iic (-x) ∪ Ioi (-x)) = 1 := by
      rw [Iic_union_Ioi, probReal_univ]
    have hsplit : stdGaussian.real (Iic (-x) ∪ Ioi (-x)) =
        stdGaussian.real (Iic (-x)) + stdGaussian.real (Ioi (-x)) :=
      measureReal_union (Set.disjoint_left.mpr fun t ht1 ht2 =>
        not_lt.mpr (mem_Iic.mp ht1) (mem_Ioi.mp ht2))
        measurableSet_Ioi (measure_ne_top _ _) (measure_ne_top _ _)
    linarith
  have h_Ioi_real : stdGaussian.real (Ioi (-x)) = stdGaussian.real (Iic x) := by
    simp only [Measure.real]; congr 1; rw [← h_Ici_Ioi, h_sym]
  linarith

/-- `Φ(0) = 1/2` by symmetry of the standard normal distribution. -/
theorem normalCDF_zero : normalCDF 0 = 1 / 2 := by
  have h := normalCDF_neg 0; simp only [neg_zero] at h; linarith

/-- The normal CDF is strictly monotone increasing. -/
theorem normalCDF_strictMono : StrictMono normalCDF := by
  intro a b hab
  simp only [normalCDF, cdf_eq_real]
  have hIic : Iic b = Iic a ∪ Ioc a b := (Iic_union_Ioc_eq_Iic (le_of_lt hab)).symm
  have hd : Disjoint (Iic a) (Ioc a b) :=
    Set.disjoint_left.mpr fun t ht1 ht2 => not_lt.mpr (mem_Iic.mp ht1) (mem_Ioc.mp ht2).1
  rw [hIic, measureReal_union hd measurableSet_Ioc (measure_ne_top _ _) (measure_ne_top _ _)]
  suffices h : 0 < stdGaussian.real (Ioc a b) by linarith
  rw [Measure.real, ENNReal.toReal_pos_iff]
  refine ⟨?_, measure_lt_top _ _⟩
  rw [stdGaussian_unfold, withDensity_apply _ measurableSet_Ioc,
      setLIntegral_pos_iff (measurable_gaussianPDF 0 1),
      support_gaussianPDF std_var_ne_zero, Set.univ_inter, volume_Ioc]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)

/-- For `x > 0`, `Φ(x) > 1/2`. -/
theorem normalCDF_pos_gt_half {x : ℝ} (hx : 0 < x) : 1 / 2 < normalCDF x := by
  rw [← normalCDF_zero]; exact normalCDF_strictMono hx

/-- For `x < 0`, `Φ(x) < 1/2`. -/
theorem normalCDF_neg_lt_half {x : ℝ} (hx : x < 0) : normalCDF x < 1 / 2 := by
  rw [← normalCDF_zero]; exact normalCDF_strictMono hx

end Core
