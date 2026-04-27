import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue

/-!
# Standard Normal Distribution Infrastructure

Pure standard-normal infrastructure: density, CDF, monotonicity, symmetry,
continuity, and the probit (inverse-CDF) function. Application-agnostic —
used by Thurstone's discriminal-process theory, Signal Detection Theory, and
any other consumer that needs Φ and Φ⁻¹ over the reals.

## Definitions

- `normalPDF`: the standard normal density φ(t) = (1/√(2π)) exp(−t²/2)
- `normalCDF`: the standard normal CDF Φ(x) = ∫_{−∞}^{x} φ(t) dt
- `probit`: the standard-normal quantile function Φ⁻¹ (with junk value 0
  outside `(0, 1)`)

The CDF is defined via Mathlib's `cdf (gaussianReal 0 1)`, grounding the
properties in Mathlib's measure-theoretic Gaussian infrastructure.

## Mathlib upstream candidates

None of `normalCDF_neg`, `normalCDF_zero`, `normalCDF_strictMono`,
`continuous_normalCDF`, `normalCDF_injective`, `normalCDF_surj_Ioo`, or
`probit` exist in mathlib (verified 2026-04-25 against `Mathlib.Probability.CDF`
and `Mathlib.Probability.Distributions.Gaussian.*`). Mathlib provides only
`cdf_nonneg`, `cdf_le_one`, `monotone_cdf`, and the `tendsto_cdf_atBot/atTop`
limits at the level of generic probability measures. The `continuous_cdf_of_noAtoms`
private lemma below is the strongest upstream candidate — it is generic for any
atomless probability measure on ℝ.
-/

namespace Core

open Real MeasureTheory BigOperators Set ProbabilityTheory NNReal Filter

/-! ## Normal PDF -/

/-- The standard normal probability density function: `φ(t) = (1/√(2π)) · exp(-t²/2)`. -/
noncomputable def normalPDF (t : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2)

/-! ## Normal CDF -/

/-- The standard normal cumulative distribution function:
    `Φ(x) = ∫_{-∞}^{x} (1/√(2π)) exp(-t²/2) dt`.

    Defined as `cdf (gaussianReal 0 1) x`, the CDF of the standard Gaussian
    measure evaluated at `x`. -/
noncomputable def normalCDF (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

/-! ## Helper lemmas for the standard Gaussian -/

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

/-! ## Properties -/

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

/-- Positive Gaussian measure on any non-empty `Ioc a b` (`a < b`). The
    workhorse for `normalCDF_strictMono` and `normalCDF_pos`. -/
private theorem stdGaussian_real_Ioc_pos {a b : ℝ} (h : a < b) :
    0 < stdGaussian.real (Ioc a b) := by
  rw [Measure.real, ENNReal.toReal_pos_iff]
  refine ⟨?_, measure_lt_top _ _⟩
  rw [stdGaussian_unfold, withDensity_apply _ measurableSet_Ioc,
      setLIntegral_pos_iff (measurable_gaussianPDF 0 1),
      support_gaussianPDF std_var_ne_zero, Set.univ_inter, volume_Ioc]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr h)

/-- The normal CDF is strictly monotone increasing. -/
theorem normalCDF_strictMono : StrictMono normalCDF := by
  intro a b hab
  simp only [normalCDF, cdf_eq_real]
  have hIic : Iic b = Iic a ∪ Ioc a b := (Iic_union_Ioc_eq_Iic (le_of_lt hab)).symm
  have hd : Disjoint (Iic a) (Ioc a b) :=
    Set.disjoint_left.mpr fun t ht1 ht2 => not_lt.mpr (mem_Iic.mp ht1) (mem_Ioc.mp ht2).1
  rw [hIic, measureReal_union hd measurableSet_Ioc (measure_ne_top _ _) (measure_ne_top _ _)]
  linarith [stdGaussian_real_Ioc_pos hab]

/-- `0 < Φ(x)` for all `x`. The standard normal CDF takes values in the
    open interval `(0, 1)` everywhere on the reals.

    Proof: pick the non-empty `Ioc (x-1) x ⊆ Iic x` and apply
    `stdGaussian_real_Ioc_pos`. -/
theorem normalCDF_pos (x : ℝ) : 0 < normalCDF x := by
  simp only [normalCDF, cdf_eq_real]
  have hsub : Ioc (x - 1) x ⊆ Iic x := fun _ ht => ht.2
  have hmono : stdGaussian.real (Ioc (x - 1) x) ≤ stdGaussian.real (Iic x) :=
    measureReal_mono hsub (measure_ne_top _ _)
  linarith [stdGaussian_real_Ioc_pos (show x - 1 < x by linarith)]

/-- `Φ(x) < 1` for all `x`. Dual of `normalCDF_pos` via the symmetry
    `Φ(-x) = 1 - Φ(x)`. -/
theorem normalCDF_lt_one (x : ℝ) : normalCDF x < 1 := by
  have h := normalCDF_pos (-x)
  rw [normalCDF_neg] at h; linarith

/-- The standard normal CDF maps into `Set.Ioo 0 1`. -/
theorem normalCDF_mem_Ioo (x : ℝ) : normalCDF x ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨normalCDF_pos x, normalCDF_lt_one x⟩

/-- For `x > 0`, `Φ(x) > 1/2`. -/
theorem normalCDF_pos_gt_half {x : ℝ} (hx : 0 < x) : 1 / 2 < normalCDF x := by
  rw [← normalCDF_zero]; exact normalCDF_strictMono hx

/-- For `x < 0`, `Φ(x) < 1/2`. -/
theorem normalCDF_neg_lt_half {x : ℝ} (hx : x < 0) : normalCDF x < 1 / 2 := by
  rw [← normalCDF_zero]; exact normalCDF_strictMono hx

/-- The normal CDF is injective (from strict monotonicity). -/
theorem normalCDF_injective : Function.Injective normalCDF :=
  normalCDF_strictMono.injective

/-! ## Continuity and surjectivity -/

/-- The CDF of an atomless probability measure is continuous.

    TODO: upstream to `Mathlib.Probability.CDF` — this works for any atomless
    probability measure on ℝ, not just the standard Gaussian. -/
private theorem continuous_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · rw [(monotone_cdf μ).continuousWithinAt_Iio_iff_leftLim_eq]
    have h_singleton : (cdf μ).measure {x} = 0 := by
      rw [measure_cdf]; exact measure_singleton x
    rw [StieltjesFunction.measure_singleton] at h_singleton
    linarith [ENNReal.ofReal_eq_zero.mp h_singleton, (monotone_cdf μ).leftLim_le (le_refl x)]
  · exact ((cdf μ).right_continuous x).mono Ioi_subset_Ici_self

/-- The standard normal CDF is continuous. -/
theorem continuous_normalCDF : Continuous normalCDF := by
  have : NoAtoms (gaussianReal (0 : ℝ) (1 : ℝ≥0)) := noAtoms_gaussianReal std_var_ne_zero
  exact continuous_cdf_of_noAtoms (gaussianReal 0 1)

/-- The standard normal CDF is surjective onto `(0, 1)`:
    for any `p ∈ (0, 1)`, there exists `x` with `Φ(x) = p`. -/
theorem normalCDF_surj_Ioo (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ x : ℝ, normalCDF x = p :=
  intermediate_value_univ₂_eventually₂ continuous_normalCDF continuous_const
    (((tendsto_cdf_atBot (gaussianReal 0 1)).eventually (Iio_mem_nhds hp0)).mono
      fun _ hx => le_of_lt hx)
    (((tendsto_cdf_atTop (gaussianReal 0 1)).eventually (Ioi_mem_nhds hp1)).mono
      fun _ hx => le_of_lt hx)

/-! ## Probit (inverse normal CDF / quantile function) -/

/-- The probit function (inverse normal CDF / quantile of the standard normal):
    for `p ∈ (0, 1)`, returns the unique `x` with `Φ(x) = p`. Returns the junk
    value `0` for inputs outside `(0, 1)`.

    Existence follows from the Intermediate Value Theorem applied to the
    continuous, strictly monotone `normalCDF` with limits 0 at -∞ and 1 at +∞.

    **Junk-value caveat**: `probit 0 = probit 1 = probit 2 = 0`. Callers that
    might pass boundary or out-of-range values should guard with `0 < p < 1`,
    or apply a continuity correction (e.g., the Hautus 1995 log-linear rule)
    before invoking. -/
noncomputable def probit (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 then
    Classical.choose (normalCDF_surj_Ioo p h.1 h.2)
  else 0

/-- Specification: `Φ(probit(p)) = p` for `p ∈ (0, 1)`. -/
theorem probit_spec {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    normalCDF (probit p) = p := by
  simp only [probit, hp0, hp1, and_self, dite_true]
  exact Classical.choose_spec (normalCDF_surj_Ioo p hp0 hp1)

/-- Specification: `probit(Φ(x)) = x` for all `x` (left inverse). -/
theorem probit_normalCDF (x : ℝ) : probit (normalCDF x) = x := by
  have hp0 : 0 < normalCDF x :=
    lt_of_le_of_lt (normalCDF_nonneg (x - 1)) (normalCDF_strictMono (by linarith))
  have hp1 : normalCDF x < 1 :=
    lt_of_lt_of_le (normalCDF_strictMono (by linarith : x < x + 1)) (normalCDF_le_one (x + 1))
  exact normalCDF_injective (probit_spec hp0 hp1)

/-- On `(0, 1)`, the probit ordering matches the input ordering exactly.
    Subsumes the strict-monotonicity direction (`probit p₁ < probit p₂`
    when `p₁ < p₂`) as `.mpr`. -/
theorem probit_lt_iff {p₁ p₂ : ℝ}
    (hp₁_lo : 0 < p₁) (hp₁_hi : p₁ < 1)
    (hp₂_lo : 0 < p₂) (hp₂_hi : p₂ < 1) :
    probit p₁ < probit p₂ ↔ p₁ < p₂ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := normalCDF_strictMono h
    rwa [probit_spec hp₁_lo hp₁_hi, probit_spec hp₂_lo hp₂_hi] at this
  · by_contra hle; push Not at hle
    have := normalCDF_strictMono.monotone hle
    rw [probit_spec hp₁_lo hp₁_hi, probit_spec hp₂_lo hp₂_hi] at this
    linarith

/-! ## Order-iso packaging

The standard normal CDF is a strictly monotone bijection between `ℝ` and
`Set.Ioo (0 : ℝ) 1`. Packaging this as an `OrderIso` gives downstream code
access to `OrderIso.lt_iff_lt`, `OrderIso.symm_apply_apply`, etc. without
the four `0 < pᵢ < 1` hypotheses that `probit_lt_iff` requires for the
junk-value-tolerant API. Both APIs are kept: the bare `probit_lt_iff` is
ergonomic for raw real inputs; the `OrderIso` is the structural form.

TODO: upstream as `Real.normalCDFOrderIso : ℝ ≃o Set.Ioo (0:ℝ) 1` to
`Mathlib.Probability.Distributions.Gaussian.Real`. -/

/-- The standard normal CDF as an order isomorphism `ℝ ≃o Set.Ioo (0:ℝ) 1`.
    Inverse is given by `probit` restricted to `(0, 1)`. -/
noncomputable def normalCDFOrderIso : ℝ ≃o Set.Ioo (0 : ℝ) 1 where
  toFun x := ⟨normalCDF x, normalCDF_mem_Ioo x⟩
  invFun p := probit p.1
  left_inv x := probit_normalCDF x
  right_inv := fun ⟨p, hp⟩ => Subtype.ext (probit_spec hp.1 hp.2)
  map_rel_iff' := normalCDF_strictMono.le_iff_le

end Core
