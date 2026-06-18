import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Moments.Basic

/-!
# The Gibbs / Donsker–Varadhan variational principle  [UPSTREAM]

For a probability measure `μ` and a function `f`, the **exponentially tilted
measure** `μ.tilted f` (`MeasureTheory.Measure.tilted`, the Gibbs measure /
Esscher transform with density `∝ exp f`) is the maximizer of the free-energy
functional `q ↦ 𝔼_q[f] − KL(q ‖ μ)`, and the maximal value is the **log-partition
function** `log ∫ exp f ∂μ`. This is the **Gibbs variational principle**
(a.k.a. **Donsker–Varadhan**), the variational characterization of the
Kullback–Leibler divergence anticipated by the module docstring of
`Mathlib/MeasureTheory/Measure/Tilted.lean`.

## Main definitions

* `MeasureTheory.Measure.logIntegralExp μ f = log (∫ x, exp (f x) ∂μ)` — the
  log-partition / free-energy functional. It generalizes the cumulant generating
  function `ProbabilityTheory.cgf` (the affine case `f = t • X`); see
  `logIntegralExp_const_mul`.

## Main statements

* `toReal_klDiv_tilted_right` — the **Gibbs decomposition identity**:
  `KL(q ‖ μ.tilted f) = KL(q ‖ μ) − 𝔼_q[f] + logIntegralExp μ f`.
* `sub_klDiv_le_logIntegralExp` — the **variational inequality**:
  `𝔼_q[f] − KL(q ‖ μ) ≤ logIntegralExp μ f` for all `q ≪ μ`.
* `sub_klDiv_tilted_eq_logIntegralExp` — the bound is **attained** at `μ.tilted f`.
* `isGreatest_logIntegralExp` — the **variational principle** in `IsGreatest` form:
  `logIntegralExp μ f` is the greatest value of `q ↦ 𝔼_q[f] − KL(q ‖ μ)`.

## Implementation notes

The decomposition reuses the log-likelihood-ratio identity
`MeasureTheory.integral_llr_tilted_right`; both `klDiv` terms collapse to their
`llr`-integrals via `toReal_klDiv_of_measure_eq` (the `univ`-mass correction in
`toReal_klDiv` vanishes because every measure in play is a probability measure —
`μ.tilted f` is normalized by construction). The statements are over probability
measures; the finite-measure generalization carries an additive `μ.real univ`
correction and is left for future work.
-/

open Real MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- The **log-partition** (free-energy) functional `log ∫ exp f ∂μ`. Generalizes
the cumulant generating function `ProbabilityTheory.cgf` to an arbitrary
integrand (the affine case `f = fun x ↦ t * X x` recovers `cgf X μ t`, see
`logIntegralExp_const_mul`). -/
noncomputable def Measure.logIntegralExp (μ : Measure α) (f : α → ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (f x) ∂μ)

/-- `logIntegralExp` generalizes the cumulant generating function: on the affine
family `f = fun x ↦ t * X x` it is `ProbabilityTheory.cgf X μ t`. -/
theorem logIntegralExp_const_mul (μ : Measure α) (X : α → ℝ) (t : ℝ) :
    μ.logIntegralExp (fun x => t * X x) = cgf X μ t := by
  simp only [Measure.logIntegralExp, cgf, mgf]

/-- **Gibbs decomposition identity**: for `q ≪ μ` (both probability measures),
the Kullback–Leibler divergence from the Gibbs measure `μ.tilted f` splits as
`KL(q ‖ μ.tilted f) = KL(q ‖ μ) − 𝔼_q[f] + logIntegralExp μ f`.

A `klDiv`-level repackaging of `integral_llr_tilted_right`: both divergences
reduce to their `llr`-integrals via `toReal_klDiv_of_measure_eq` (the mass
correction vanishes — all measures are probability measures), after which the
log-likelihood-ratio decomposition closes it. -/
theorem toReal_klDiv_tilted_right (μ q : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure q] {f : α → ℝ} (hqμ : q ≪ μ)
    (h_int_llr : Integrable (llr q μ) q) (h_int_f : Integrable f q)
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    (klDiv q (μ.tilted f)).toReal
      = (klDiv q μ).toReal - (∫ x, f x ∂q) + μ.logIntegralExp f := by
  have h_prob_tilt : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_exp
  have hq_tilt : q ≪ μ.tilted f := hqμ.trans (absolutelyContinuous_tilted h_exp)
  rw [toReal_klDiv_of_measure_eq hq_tilt (by rw [measure_univ, measure_univ]),
      toReal_klDiv_of_measure_eq hqμ (by rw [measure_univ, measure_univ]),
      integral_llr_tilted_right hqμ h_int_f h_exp h_int_llr, Measure.logIntegralExp]

/-- **Gibbs / Donsker–Varadhan variational inequality**: for every probability
measure `q ≪ μ`, expected value minus relative entropy is bounded by the
log-partition function, `𝔼_q[f] − KL(q ‖ μ) ≤ logIntegralExp μ f`. Immediate from
the decomposition identity and `0 ≤ KL`. -/
theorem sub_klDiv_le_logIntegralExp (μ q : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure q] {f : α → ℝ} (hqμ : q ≪ μ)
    (h_int_llr : Integrable (llr q μ) q) (h_int_f : Integrable f q)
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    (∫ x, f x ∂q) - (klDiv q μ).toReal ≤ μ.logIntegralExp f := by
  have h := toReal_klDiv_tilted_right μ q hqμ h_int_llr h_int_f h_exp
  have hnn : 0 ≤ (klDiv q (μ.tilted f)).toReal := ENNReal.toReal_nonneg
  linarith

/-- The variational bound `sub_klDiv_le_logIntegralExp` is **attained** at the
Gibbs measure `μ.tilted f`: `𝔼_{μ.tilted f}[f] − KL(μ.tilted f ‖ μ) =
logIntegralExp μ f`. Immediate from the decomposition at `q = μ.tilted f`, where
the relative-entropy term `KL(μ.tilted f ‖ μ.tilted f)` vanishes. -/
theorem sub_klDiv_tilted_eq_logIntegralExp (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (h_int_f : Integrable f (μ.tilted f))
    (h_int_llr : Integrable (llr (μ.tilted f) μ) (μ.tilted f))
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    (∫ x, f x ∂(μ.tilted f)) - (klDiv (μ.tilted f) μ).toReal = μ.logIntegralExp f := by
  have h_prob_tilt : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_exp
  have h := toReal_klDiv_tilted_right μ (μ.tilted f) (tilted_absolutelyContinuous μ f)
    h_int_llr h_int_f h_exp
  rw [klDiv_self, ENNReal.toReal_zero] at h
  linarith

/-- **Gibbs / Donsker–Varadhan variational principle**: the log-partition
function `logIntegralExp μ f` is the *greatest* value of the free-energy
functional `q ↦ 𝔼_q[f] − KL(q ‖ μ)` over probability measures `q ≪ μ` (with the
relevant integrability), the maximum being attained at the Gibbs measure
`μ.tilted f`. Bundles `sub_klDiv_le_logIntegralExp` (upper bound) and
`sub_klDiv_tilted_eq_logIntegralExp` (attainment). -/
theorem isGreatest_logIntegralExp (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (h_int_f : Integrable f (μ.tilted f))
    (h_int_llr : Integrable (llr (μ.tilted f) μ) (μ.tilted f))
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    IsGreatest
      {x : ℝ | ∃ q : Measure α, IsProbabilityMeasure q ∧ q ≪ μ ∧
        Integrable (llr q μ) q ∧ Integrable f q ∧
        x = (∫ a, f a ∂q) - (klDiv q μ).toReal}
      (μ.logIntegralExp f) := by
  refine ⟨⟨μ.tilted f, isProbabilityMeasure_tilted h_exp, tilted_absolutelyContinuous μ f,
      h_int_llr, h_int_f, (sub_klDiv_tilted_eq_logIntegralExp μ h_int_f h_int_llr h_exp).symm⟩, ?_⟩
  rintro x ⟨q, hq_prob, hqμ, hq_llr, hq_f, rfl⟩
  haveI := hq_prob
  exact sub_klDiv_le_logIntegralExp μ q hqμ hq_llr hq_f h_exp

end MeasureTheory
