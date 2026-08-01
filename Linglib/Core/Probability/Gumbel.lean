import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Gumbel distribution

The Gumbel (Type I extreme value) distribution over ℝ, in the register of
`Mathlib.Probability.Distributions.*`: density → measure via `withDensity` →
CDF as a theorem. Application-agnostic — the random-utility reading lives in
`Core/Probability/Choice/GumbelLuce.lean`.

## Main definitions

* `gumbelPDFReal`: the density `β⁻¹ · exp(-(x-μ)/β) · exp(-exp(-(x-μ)/β))`
  with location `μ` and scale `β`.
* `gumbelPDF`: the ℝ≥0∞-valued density.
* `gumbelMeasure`: the Gumbel measure, `volume.withDensity (gumbelPDF μ β)`.

## Main results

* `cdf_gumbelMeasure_eq`: the CDF is `exp(-exp(-(x-μ)/β))`.
* `prod_cdf_gumbelMeasure`: max-stability — the product of Gumbel CDFs with
  common scale is the Gumbel CDF at location `β * log (∑ exp (uⱼ/β))`.
* `integral_gumbelPDFReal_mul_prod_cdf`: the max-probability integral of a
  Gumbel random-utility family evaluates to `exp(uᵢ/β) / ∑ⱼ exp(uⱼ/β)`.

## Mathlib upstream candidates

Mathlib has no Gumbel (or any extreme-value) distribution (verified 2026-08-01
against `Mathlib.Probability.Distributions.*`); this whole file follows the
`Pareto.lean` template and is an upstream candidate. `integrableOn_gumbelPDFReal_Iic`
inlines a reflection argument because mathlib has `integrableOn_Ioi_deriv_of_nonneg'`
but no `Iic` mirror — that general lemma is a separate small upstream candidate.
-/

namespace Core

open scoped ENNReal NNReal
open MeasureTheory Real Set Filter Topology ProbabilityTheory

variable {μ β x : ℝ}

/-! ### Density -/

section GumbelPDF

/-- The pdf of the Gumbel distribution with location `μ` and scale `β`. -/
noncomputable def gumbelPDFReal (μ β x : ℝ) : ℝ :=
  β⁻¹ * exp (-((x - μ) / β)) * exp (-exp (-((x - μ) / β)))

/-- The pdf of the Gumbel distribution, as a function valued in `ℝ≥0∞`. -/
noncomputable def gumbelPDF (μ β x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gumbelPDFReal μ β x)

@[fun_prop]
lemma measurable_gumbelPDFReal (μ β : ℝ) : Measurable (gumbelPDFReal μ β) := by
  unfold gumbelPDFReal; fun_prop

@[fun_prop]
lemma stronglyMeasurable_gumbelPDFReal (μ β : ℝ) :
    StronglyMeasurable (gumbelPDFReal μ β) := (measurable_gumbelPDFReal μ β).stronglyMeasurable

lemma gumbelPDFReal_pos (hβ : 0 < β) (μ x : ℝ) : 0 < gumbelPDFReal μ β x := by
  unfold gumbelPDFReal; positivity

lemma gumbelPDFReal_nonneg (hβ : 0 ≤ β) (μ x : ℝ) : 0 ≤ gumbelPDFReal μ β x := by
  unfold gumbelPDFReal; positivity

/-- The Gumbel cdf `exp (-exp (-(x - μ)/β))` is an antiderivative of the pdf. -/
lemma hasDerivAt_gumbelCDF (μ β x : ℝ) :
    HasDerivAt (fun y => exp (-exp (-((y - μ) / β)))) (gumbelPDFReal μ β x) x := by
  have h : HasDerivAt (fun y => -exp (-((y - μ) / β)))
      (-(exp (-((x - μ) / β)) * -(1 / β))) x :=
    ((Real.hasDerivAt_exp _).comp x (((hasDerivAt_id x).sub_const μ).div_const β).neg).neg
  refine h.exp.congr_deriv ?_
  simp only [gumbelPDFReal]; ring

lemma tendsto_gumbelCDF_atTop (hβ : 0 < β) (μ : ℝ) :
    Tendsto (fun y => exp (-exp (-((y - μ) / β)))) atTop (𝓝 1) := by
  have hz : Tendsto (fun y : ℝ => -((y - μ) / β)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp ((tendsto_atTop_add_const_right _ (-μ)
      tendsto_id).atTop_div_const hβ |>.congr (by intro y; simp only [id_eq]; ring))
  simpa [Function.comp_def] using
    (continuous_exp.tendsto 0).comp (by simpa using (tendsto_exp_atBot.comp hz).neg)

lemma tendsto_gumbelCDF_atBot (hβ : 0 < β) (μ : ℝ) :
    Tendsto (fun y => exp (-exp (-((y - μ) / β)))) atBot (𝓝 0) := by
  have hz : Tendsto (fun y : ℝ => -((y - μ) / β)) atBot atTop :=
    tendsto_neg_atBot_atTop.comp ((tendsto_atBot_add_const_right _ (-μ)
      tendsto_id).atBot_div_const hβ |>.congr (by intro y; simp only [id_eq]; ring))
  exact tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_exp_atTop.comp hz))

lemma integrableOn_gumbelPDFReal_Ioi (hβ : 0 < β) (μ a : ℝ) :
    IntegrableOn (gumbelPDFReal μ β) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_gumbelCDF μ β x)
    (fun x _ => (gumbelPDFReal_pos hβ μ x).le) (tendsto_gumbelCDF_atTop hβ μ)

lemma integrableOn_gumbelPDFReal_Iic (hβ : 0 < β) (μ a : ℝ) :
    IntegrableOn (gumbelPDFReal μ β) (Iic a) := by
  have hrefl : IntegrableOn (fun x => gumbelPDFReal μ β (-x)) (Ioi (-a)) :=
    integrableOn_Ioi_deriv_of_nonneg' (g := fun x => -exp (-exp (-((-x - μ) / β))))
      (fun x _ => (((hasDerivAt_gumbelCDF μ β (-x)).comp x (hasDerivAt_neg x)).neg).congr_deriv
        (by ring))
      (fun x _ => (gumbelPDFReal_pos hβ μ (-x)).le)
      (by simpa [Function.comp_def] using
        ((tendsto_gumbelCDF_atBot hβ μ).comp tendsto_neg_atTop_atBot).neg)
  refine ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (MeasurableEquiv.neg ℝ).measurableEmbedding).mp ?_
  rw [show Neg.neg ⁻¹' (Iic a) = Ici (-a) from by ext y; simp,
    integrableOn_Ici_iff_integrableOn_Ioi]
  simpa [Function.comp_def] using hrefl

lemma integrable_gumbelPDFReal (hβ : 0 < β) (μ : ℝ) : Integrable (gumbelPDFReal μ β) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact (integrableOn_gumbelPDFReal_Iic hβ μ 0).union (integrableOn_gumbelPDFReal_Ioi hβ μ 0)

/-- The pdf of the Gumbel distribution integrates to `1`. -/
lemma integral_gumbelPDFReal_eq_one (hβ : 0 < β) (μ : ℝ) : ∫ x, gumbelPDFReal μ β x = 1 := by
  simpa using integral_of_hasDerivAt_of_tendsto (fun x => hasDerivAt_gumbelCDF μ β x)
    (integrable_gumbelPDFReal hβ μ) (tendsto_gumbelCDF_atBot hβ μ) (tendsto_gumbelCDF_atTop hβ μ)

@[simp]
lemma lintegral_gumbelPDF_eq_one (hβ : 0 < β) (μ : ℝ) : ∫⁻ x, gumbelPDF μ β x = 1 := by
  simp only [gumbelPDF]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gumbelPDFReal hβ μ)
    (.of_forall fun x => gumbelPDFReal_nonneg hβ.le μ x), integral_gumbelPDFReal_eq_one hβ μ,
    ENNReal.ofReal_one]

end GumbelPDF

/-! ### Measure and CDF -/

/-- Measure defined by the Gumbel distribution. -/
noncomputable def gumbelMeasure (μ β : ℝ) : Measure ℝ := volume.withDensity (gumbelPDF μ β)

lemma isProbabilityMeasure_gumbelMeasure (hβ : 0 < β) (μ : ℝ) :
    IsProbabilityMeasure (gumbelMeasure μ β) where
  measure_univ := by simp [gumbelMeasure, lintegral_gumbelPDF_eq_one hβ μ]

section GumbelCDF

lemma cdf_gumbelMeasure_eq_integral (hβ : 0 < β) (μ x : ℝ) :
    cdf (gumbelMeasure μ β) x = ∫ y in Iic x, gumbelPDFReal μ β y := by
  have : IsProbabilityMeasure (gumbelMeasure μ β) := isProbabilityMeasure_gumbelMeasure hβ μ
  rw [cdf_eq_real, gumbelMeasure, measureReal_def, withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun y => gumbelPDFReal_nonneg hβ.le μ y
  · fun_prop

/-- The cdf of the Gumbel distribution is `exp (-exp (-(x - μ)/β))`. -/
lemma cdf_gumbelMeasure_eq (hβ : 0 < β) (μ x : ℝ) :
    cdf (gumbelMeasure μ β) x = exp (-exp (-((x - μ) / β))) := by
  rw [cdf_gumbelMeasure_eq_integral hβ μ x,
    integral_Iic_of_hasDerivAt_of_tendsto' (fun y _ => hasDerivAt_gumbelCDF μ β y)
      (integrableOn_gumbelPDFReal_Iic hβ μ x) (tendsto_gumbelCDF_atBot hβ μ), sub_zero]

end GumbelCDF

/-! ### Max-stability and the max-probability integral -/

section MaxStability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private lemma sum_exp_pos (u : ι → ℝ) (β : ℝ) : (0:ℝ) < ∑ j : ι, exp (u j / β) :=
  Finset.sum_pos (fun _ _ => exp_pos _) ⟨Classical.arbitrary ι, Finset.mem_univ _⟩

/-- **Max-stability of the Gumbel family**: the product of independent Gumbel
CDFs with common scale `β` is Gumbel with scale `β` and location
`β * log (∑ exp (uⱼ/β))`. -/
theorem prod_cdf_gumbelMeasure (u : ι → ℝ) (hβ : 0 < β) (x : ℝ) :
    ∏ j : ι, cdf (gumbelMeasure (u j) β) x
      = cdf (gumbelMeasure (β * log (∑ j : ι, exp (u j / β))) β) x := by
  simp only [cdf_gumbelMeasure_eq hβ, ← exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [show -((x - β * log (∑ j : ι, exp (u j / β))) / β)
        = log (∑ j : ι, exp (u j / β)) + -(x/β) from by field_simp; ring,
      exp_add, exp_log (sum_exp_pos u β), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show -((x - u j) / β) = u j / β + -(x/β) from by ring, exp_add]

/-- The max-probability integral of a Gumbel random-utility family: the density
formula for the event that alternative `i` attains the maximum evaluates to
`exp(uᵢ/β) / ∑ⱼ exp(uⱼ/β)`. -/
theorem integral_gumbelPDFReal_mul_prod_cdf [DecidableEq ι] (u : ι → ℝ) (hβ : 0 < β)
    (i : ι) :
    (∫ x, gumbelPDFReal (u i) β x *
        ∏ j ∈ Finset.univ.erase i, cdf (gumbelMeasure (u j) β) x)
      = exp (u i / β) / ∑ j : ι, exp (u j / β) := by
  have key : ∀ x : ℝ, gumbelPDFReal (u i) β x * ∏ j ∈ Finset.univ.erase i,
      cdf (gumbelMeasure (u j) β) x
      = exp (u i / β) / (∑ j : ι, exp (u j / β)) *
          gumbelPDFReal (β * log (∑ j : ι, exp (u j / β))) β x := by
    intro x
    rw [show ∏ j ∈ Finset.univ.erase i, cdf (gumbelMeasure (u j) β) x
        = (∏ j : ι, cdf (gumbelMeasure (u j) β) x) / cdf (gumbelMeasure (u i) β) x from by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      field_simp [cdf_gumbelMeasure_eq hβ, exp_ne_zero],
      prod_cdf_gumbelMeasure u hβ x, cdf_gumbelMeasure_eq hβ, cdf_gumbelMeasure_eq hβ]
    simp only [gumbelPDFReal]
    rw [show -((x - β * log (∑ j : ι, exp (u j / β))) / β)
          = log (∑ j : ι, exp (u j / β)) + -(x/β) from by field_simp; ring,
      exp_add, exp_log (sum_exp_pos u β),
      show -((x - u i) / β) = u i / β + -(x/β) from by ring, exp_add]
    field_simp
  simp_rw [key, integral_const_mul, integral_gumbelPDFReal_eq_one hβ, mul_one]

end MaxStability

end Core
